/*
 * 20131018_i2lchv_rPI-linux
 *
 * Network interface to the LeCroy 1461, 1469 & 1471 HV modules based on a Raspberry Pi
 * 
 * The rPI communicates with the LeCroy HV modules via UART.
 * The baud-rate is 38.4 kbaud
 * There is no flow control (the LeCroy HV modules have none).
 *
 * This code uses telnet (with port# 24742) to receive commands and to send back responses
 * from the high-voltage modules.
 * 
 * Command format (upper or lower case can be used):
 *
 * SLOT# SUBMODULE# module-cmd-syntax		(high-voltage module command )
 * _Q        								(quit)
 * _LL     								(prints summary of module/submodle found)
 * _CLI      								(clears the output buffers of all HV modules)
 *
 *
 * JG
 */


#define BASE_PORT	24742

#define  L16          16
#define  L256         256
#define  L4096        4096
#define  USCHAR		   260  /* 260 microseconds per character @ 38.4 kB (module baud rate) */
#define  NTRIES         10  /* read attempts to get complete module response */ 
#define  nSLOTS         16  /* number of slots in a crate */
#define  nSUBMOD         2  /* maximum number of sumbmodules in a HV module */
#define  nLU            (nSLOTS * nSUBMOD) /* number of logic units */
#define  nLUTYP          8  /* Number of different logic unit types */

#define  MSGstat_NONE    -2 /* no message was received */
#define  MSGstat_noEOM   -1 /* failed to find end-of-message sequence */
#define  MSGstat_noACK    0 /* module did not set ACK in message */
#define  MSGstat_OK       1 /* message */
#define  MSGstat_HNDSHK   2 /* message is the handshake sequence */

#define  ABNORMAL  -1 /* encoutered unexpected condition */
#define  NORMAL     0 /* as expected */

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <fcntl.h>
#include <math.h>
#include <string.h>
/* #include <sys/termios.h> */
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <time.h>

/* Logic Unit Structure - holds information about each logic unit */
struct LUnit
  {
  unsigned char hdr[L256];
  unsigned char ack[L16];
  unsigned char id[L256];
  int  lutype;
  int  slot;
  int  nsmod; /* number of sub-modules */
  int  smod;  /* sub-module number */
  };

struct LUnit *pLU[nLU], *pLUtmp;
int lstLU = -1;
int SS2LU[nSLOTS][nSUBMOD]; /* map of slot-submodule to logic unit */
int SLOTwMOD[nSLOTS], nMOD = 0; /* slots with module in them */

/* serial port  variables */
int sio, mdlns;
struct termios sio_attr;
unsigned char sio_TXbuff[L256];
int           sio_TXlen;
unsigned char sio_dmpTXbuff = 0;
unsigned char sio_RXbuff[L256];
int           sio_RXlen;
unsigned char sio_dmpRXbuff = 0;
unsigned char sio_MSGbuff[L4096];
int           sio_MSGlen;

/* Network variables */
unsigned char nio_RXbuff[L4096]; /* receive buffer */
int           nio_RXlen; /* received message length */
unsigned char nio_TXbuff[L4096]; /* transmit buffer */
int           nio_TXlen; /* Network - transmit buffer length */
unsigned char nio_quit = 0; /* close connection */

/* prompt for perl shim server */
unsigned char *prompt="hvpi>"; 

/* global error reporting */
int errno;

/* to access GPIO pins */
static volatile uint32_t  *gpioReg = MAP_FAILED;


/* ================================================================================
 * 
 * Checks for wait_sec for gpio pin to be set  
 *
 * ================================================================================
 */
int IsGpioSet(unsigned gpio, float wait_sec)
  {
  unsigned bank = 0, bit;
  int ntry=0, iloop;
   
  /* The Broadcom BCM2835 processor has two registers holding the levels of the 
   * 54 GPIO pins known to the system - 32 are in the first register, the remaining 22
   * are in the second register
   */
  if(gpio > 31) bank = 1;
  bit = (1<<(gpio&0x1F));
  ntry = wait_sec*200.0; /* we check pin status every 5 millisec or 200 times/sec */
  
  for(iloop=0; iloop < ntry; iloop++) 
     {
     /* Bank = 0 is the 13teen register from the base */
     if ((*(gpioReg + 13 + bank) & bit) == 0) return NORMAL;
     usleep(5000); /* sleep for 5 milliseconds */
     }
   return ABNORMAL;
   }


/* ======================================================================================
 *
 * Retrieve a message from serial port buffer.
 * (A) It waits the equivalent of nchars * USCHAR before each buffer retrieve.
 * (B) If no character is received on the first attempt, it returns with status -2
 * (C) It then attempts multiple retrieves (10 maximum) until either it does not get
 * any further response or it finds the sequence 0x0d,0x0a (CR,LF) used by the LeCroy
 * HV modules to signal an end-of-message.
 * (D) If an end-of-message terminator was found, it checks if the message received
 * is the 3-byte handshake sequence 0x06,0x0d,0x0a (ACK,CR,LF).
 * 
 * Return codes,
 *  -2  = no message received / other error
 *  -1  = incomplete transaction: end-of-message sequence not found
 *   0  = transaction has end-of-message sequence but no acknowledge (asserted NAK [0x15] likely)
 *   1  = normal transaction: ACK, content, end-of-message sequence
 *   2  = message received is the 3-byte handshake sequence (content is 0 bytes)
 *
 * =======================================================================================
 */
int msgget(int nchar)
  {
  /* nchar is the expected number of characters in the transaction */
  int iloop, stat, indx;
   
  iloop = 0;
  stat = MSGstat_NONE;
  sio_MSGbuff[0] = '\0';
  sio_MSGlen = 0;
  
  while(iloop < NTRIES) /* attempt to get complete message */
    {
    sio_RXlen = 0;
    sio_RXbuff[0] = '\0';
    iloop = iloop + 1;
    usleep(USCHAR * nchar);
	sio_RXlen = read(sio,sio_RXbuff,L256-1);
	if(sio_RXlen > 0 )
      {
      sio_RXbuff[sio_RXlen] = '\0';
      strcat(sio_MSGbuff,sio_RXbuff);
      sio_MSGlen = strlen(sio_MSGbuff);
         
      /* check for end-of-message sequence */
      if(
        (sio_MSGbuff[sio_MSGlen - 2] == 0x0d) && /* byte before last should be CR */
        (sio_MSGbuff[sio_MSGlen - 1] == 0x0a) /* last byte should be LF */
        )
        {
        /* found end-of-message sequence */
        /* check that 1st byte is the ACK (0x06).
         * Module could signal that it is not ready by setting this byte to NAK (0x15)
         */
        if(sio_MSGbuff[0] != 0x06)
          {
          stat = MSGstat_noACK; /* end-of-message sequence but no ACK */
          }
        else
          {
          stat = MSGstat_OK; /* end-of-message sequence and ACK */
          
          /* check if this is a handshake - we already know that ACK,CR & LF are in the buffer.
           * So, we only need to check that the buffer length is 3-bytes
           */
          if(sio_MSGlen == 3) stat = MSGstat_HNDSHK;
          }
                                  
        /* we are done - exit while */
        break;
        }
      
      /* data has been received but the end-of-message sequence was not found */
      stat = MSGstat_noEOM;
      }
    else
      {
      /* no response at all - bail out */
      break;
      }
    }
         
  /* return */
  return stat;  
  };



/* =====================================================================================
 *
 * Basic command processing:
 *   - check for expected number of arguments
 *   - process global commands (e.g. _Q, _LL, ....)
 *   - check that requested module/submodule exists 
 *
 * Return codes,
 *  -1 = command failed = ABNORMAL
 *   0 = command OK = NORMAL
 * =====================================================================================
 */   
int cmdEXE(void)
  {
  unsigned char s1[L4096], s2[L4096], tmp[L4096];
  unsigned char *ps1;
  int slot, sm, i1, i2, i3;
  int status;


  status = ABNORMAL; /* set status to fail by default */
  nio_TXbuff[0] = '\0';
  nio_TXlen = 0;
  nio_RXbuff[nio_RXlen] = '\0';
  s1[0] = '\0';
  
  /* Commands must be in upper-case characters */
  for(i1=0;i1<nio_RXlen;i1++) s1[i1] = toupper(nio_RXbuff[i1]);
  s1[nio_RXlen] = '\0';
  ps1 = strchr(s1,'\r'); /* search for CR character */
/***  ps1 = strchr(s1,'\n'); ***//* search for CR character */

  *ps1 = '\0';  /* replace CR by NULL to terminate string */
  
  i1=0;
  while(s1[i1] == ' ') /* get rid of leading spacings */
  	{
  	i1 = i1+1;
  	if(s1[i1] == '\0') return status; /* unexpected end of string */
  	}
  	
  /* is this the quit command? */
  if(strncmp(&s1[i1],"_Q",2) == 0)
    {
    nio_quit = 1;
    return NORMAL;
    }

  /* is this the dump module/submodule summary command? */
  if(strncmp(&s1[i1],"_LL",3) == 0)
    {
    printf("cmdEXE: got _LL : %s\n", nio_TXbuff);	
 
    nio_TXbuff[0] = '\0';    
/***    for(i2 = 0; i2 <= lstLU ; i2++) ***/
      {
      tmp[0] = '\0';      
/****      sprintf(tmp,"%d %s\n",pLU[i2]->slot,pLU[i2]->id);
12-May_2014
****/
      sprintf(tmp,"%d %s\r\n", 1, "1461N 0 1  11 12 B51884  -1  1000  1.135");
      strcat(nio_TXbuff,tmp);
      }      
    nio_TXlen = strlen(nio_TXbuff);
    printf("cmdEXE: return from _LL : %s\n", nio_TXbuff);	
    return NORMAL;
    }
	
  /* is this a request to clear all modules response buffers?
   * this will clear any module holding the ATN* line with a message to be delivered
   */
  if(strncmp(&s1[i1],"_CLI",4) == 0)
    {
    for(i2 = 0; i2 < nMOD; i2++) /* loop over slots with modules */
      {
      /* Load handshake message into SIO TX buffer */
      sio_TXbuff[0] = '\0';
      strcpy(sio_TXbuff,pLU[SS2LU[SLOTwMOD[i2]][0]]->ack);
      sio_TXlen = strlen(sio_TXbuff);
	  write(sio,sio_TXbuff,sio_TXlen); /* send message */
         
      /* get buffer content of module (if any)
       * response may be an ACK sequence if nothing to xfer
       * Set time wait = equivalent to 50 characters xfer (~ 13ms)
       * return status does not matter - we are just forcing a buffer dump
       */ 
      msgget(50);
      }
    return NORMAL;
    }
  	  
  /* if this a properly composed message, this substring must be the slot# */
  i2 = i1; /* index in s1 where we are */
  while(s1[i2] != ' ')
    {
    i3 = s1[i2]; /* get character */
    if(isdigit(i3) == 0) return status; /* should be a digit */
    i2 = i2+1;
    if(s1[i2] == '\0') return status; /* unexpected end of string */
    }
  s2[0] = '\0';
  strncpy(s2,&s1[i1],i2-i1);
  s2[i2-i1] = '\0';
  sscanf(s2,"%d",&slot); /* slot number */
  if((slot < 0) || (slot >= nSLOTS)) return status; /* out of range slot# */

  /* get rid of space(s) between slot# and submodule# */
  i1 = i2;
  while(s1[i1] == ' ')
  	{
  	i1 = i1+1;
  	if(s1[i1] == '\0') return status; /* unexpected end of string */
  	}

  /* the next substring must be the submodule# */
  i2 = i1; /* index in s1 where we are */
  while(s1[i2] != ' ')
    {
    i3 = s1[i2]; /* get character */
    if(isdigit(i3) == 0) return status; /* should be a digit */
    i2 = i2+1;
    if(s1[i2] == '\0') return status; /* unexpected end of string */
    }
  s2[0] = '\0';
  strncpy(s2,&s1[i1],i2-i1);
  s2[i2-i1] = '\0';
  sscanf(s2,"%d",&sm); /* submodule number */
  if((sm < 0) || (sm >= nSUBMOD)) return status; /* out of range submodule# */
 
  /* check that there is a ubit at this slot/submodule address */
  if(SS2LU[slot][sm] < 0) return status;
  
  /* get rid of space(s) between submodule# and module-cmd-syntax
   * the space is already stored in the module header
   */
  i1 = i2;
  while(s1[i1] == ' ')
  	{
  	i1 = i1+1;
  	if(s1[i1] == '\0') return status; /* unexpected end of string */
  	}
  /* Prepare and send message to module */
  sio_TXbuff[0] = '\0';
  strcpy(sio_TXbuff,pLU[SS2LU[slot][sm]]->hdr);
  strcat(sio_TXbuff,&s1[i1]);
  strcat(sio_TXbuff,"\n");  
  sio_TXlen = strlen(sio_TXbuff);
  write(sio,sio_TXbuff,sio_TXlen);
  if(msgget(sio_TXlen+50) != MSGstat_HNDSHK) return status; /* get handshake */
         
  /* wait up-to 2 sec for module to indicate is ready to send response to previous command */
  if(IsGpioSet(23,2.0) != NORMAL) return ABNORMAL;
  
  sio_TXbuff[0] = '\0';
  strcpy(sio_TXbuff,pLU[SS2LU[slot][sm]]->ack);
  sio_TXlen = strlen(sio_TXbuff);
  write(sio,sio_TXbuff,sio_TXlen);
  if(msgget(50) == MSGstat_OK) /* 50 char wait (13ms) */
    {
    nio_TXbuff[0] = '\0';
    strcpy(nio_TXbuff,&sio_MSGbuff[1]); /* skip ACK byte */
/***
    tmp[0] = '\0';      
    sprintf(tmp,"(%d,%d): ", slot, sm);
    strcat(tmp, nio_TXbuff);
***/
    nio_TXlen = strlen(nio_TXbuff);
    return NORMAL;
    }
   
  return status;
  }


/* =====================================================================================
 *
 * Command Task - commands arriving through the network connection are re-directed to
 * the high-voltage modules. Module responses are sent back through the same network
 * connection
 *
 * =====================================================================================
 */
static void cmdTSK(int connection_fd)
 {
  unsigned char tmp[L256];
  time_t now;
  int len=0;
  unsigned char *pchar;
  unsigned short psum1=0, psum2=0;
  for(;;)
    {
	/*nio_RXbuff[0] = '\0';
	nio_TXbuff[0] = '\0';*/
	memset(nio_RXbuff, '\0', sizeof(nio_RXbuff)); 
	memset(nio_TXbuff, '\0', sizeof(nio_TXbuff)); 
	nio_RXlen=0;
	nio_RXlen=read(connection_fd, nio_RXbuff, L4096-1);
/***        do {
	  len = read(connection_fd, &nio_RXbuff[len], L4096-1);
	  nio_RXlen+=len;
        }
        while( (len>0) && (nio_RXlen<=256));
***/
	/* nio_RXlen = read(fd, nio_RXbuff, 1); */
	
	if(nio_RXlen <= 0)
	  {
	  /* either the client closed the connection before sending any data or
	   * there is a problem with the connection - bail out
	   *
	   * printf("cmdTSK - error receiving message....\n");
	   */
	  break;
	  }
      else
      {
	  /* pass command to module (emulate)*/
/**** 16-May-2014 emulation ***/
	time(&now); 
	printf(" %s ", ctime(&now));	 	
	printf("cmdTSK (%d): %s\n", nio_RXlen, nio_RXbuff);
	/*tmp[0] = '\0'; */
	memset(tmp, '\0', sizeof(tmp)); 		
	if(strncmp(&nio_RXbuff[0],"_LL",3) != 0) {
	        /*tmp[0] = '\0';  */
		if(strncmp(&nio_RXbuff[4],"HVSTATUS",8) == 0) { /** HVSTATUS command **/
	           strcpy(nio_TXbuff,"1 HVSTATUS HVOFF\r\n");	
		}
		else if(strncmp(&nio_RXbuff[4],"ID",2) == 0) { /** ID command **/
	           strcpy(nio_TXbuff,"1 ID 1461N 0 1  11 12 B51884 -1 1000 1.135\r\n");	
		}
		else if(strncmp(&nio_RXbuff[4],"PROP",4) == 0) { /** PROP command **/
	           strcpy(nio_TXbuff,"1 PROP MC MV DV RUP RDN TC CE ST MVDZ MCDZ HVL\r\n");	
		}
		else if(strncmp(&nio_RXbuff[4],"ATTR",4) == 0) { /** ATTR command **/
		    pchar=&nio_RXbuff[9];
	            /*printf(" cmdTsk: strncmp(): %s", pchar);*/
		    strncpy(tmp, pchar, (nio_RXlen-11)); /* copy propertiy name without '\r\n'*/
		    sprintf(nio_TXbuff,"1 ATTR %s", tmp);
	            if(strncmp(tmp,"DV",2) == 0)  /** DV property **/    	
	              strcat(nio_TXbuff," Target_V V N N -3000.0_0.0_0.5 %7.1lf\r\n"); /* set of attributes for DV */	
	            else if(strncmp(tmp,"CE",2) == 0)  /** CE property **/    	
		      strcat(nio_TXbuff," CE_En na P N En_Ds %2s\r\n"); /* set of attributes for CE */
	            else if(strncmp(tmp,"RUP",3) == 0)  /** RUP property **/    	
		      strcat(nio_TXbuff," RUP_V/s V/s P N 50_1000_10 %7.1f\r\n"); /* set of attributes for RUP */
	            else if(strncmp(tmp,"RDN",3) == 0)  /** RDN property **/    	
		      strcat(nio_TXbuff," RDN_V/s V/s P N 50_1000_10 %7.1f\r\n"); /* set of attributes for RDN */
	            else if(strncmp(tmp,"ST",2) == 0)  /** ST property **/    	
		      strcat(nio_TXbuff," Status na M N 2 %2x\r\n"); /* set of attributes for ST */	
	            else if(strncmp(tmp,"MVDZ",4) == 0)  /** MVDZ property **/    	
		      strcat(nio_TXbuff," MV_Zone V N N 0_3000 %8f\r\n"); /* set of attributes for MVDZ */	
	            else if(strncmp(tmp,"MCDZ",4) == 0)  /** MCDZ property **/    	
		      strcat(nio_TXbuff," MC_Zone uA N N 0_3000 %8f\r\n"); /* set of attributes for MCDZ */	
	            else if(strncmp(tmp,"TC",2) == 0)  /** TC property **/    	
		      strcat(nio_TXbuff," Trip_uA uA P N 1000_10_1 %7.1f\r\n"); /* set of attributes for TC */	
	            else if(strncmp(tmp,"HVL",3) == 0)  /** HVL property **/    	
		      strcat(nio_TXbuff," HVL_V V P N -3000_0_0.5 %7.1f\r\n"); /* set of attributes for HVL */	
	            else if(strncmp(tmp,"MV",2) == 0) { /** MV property **/    	
		      strcat(nio_TXbuff," Meas_V V M N 7 %7.1lf\r\n"); /* set of attributes for MV */			     
		    }
	            else if(strncmp(tmp,"MC",2) == 0)  /** MC property **/    	
		      strcat(nio_TXbuff," Current_uA uA M N 7 %7.1lf\r\n"); /* set of attributes for MC */

	   	    else	
	              strcat(nio_TXbuff," None_N N M N 7 %7.1lf\r\n"); /* one set of attributes for all properties */	
		}
		else if(strncmp(&nio_RXbuff[4],"PSUM",4) == 0) { /** PSUM command **/
	           sprintf(nio_TXbuff,"1 PSUM %04X %04X 0000 0000 0000 0000 0000 00A8 0000 0000 0001\r\n", psum1, psum2); 	         
	           psum1++; psum2++;	
		}
		else if(strncmp(&nio_RXbuff[4],"RC",2) == 0) { /** RC command **/
		    pchar=&nio_RXbuff[7];
	            /*printf(" cmdTsk: strncmp(): %s", pchar);*/
		    strncpy(tmp, pchar, (nio_RXlen-9)); /* copy property name without '\r\n'*/
		    sprintf(nio_TXbuff,"1 RC %s", tmp);    	
	            if(strncmp(tmp,"DV",2) == 0)  /** DV property **/    	
			strcat(nio_TXbuff, " 0 0 0 0 0 0 0 0 0 0 0 0\r\n");
	            else if(strncmp(tmp,"CE",2) == 0)  /** CE property **/    	
			strcat(nio_TXbuff, " 1 0 0 0 0 0 0 0 0 0 0 0\r\n");
	            else if(strncmp(tmp,"RUP",3) == 0)  /** RUP property **/    	
			strcat(nio_TXbuff, " 50.0 50.0 50.0 50.0 50.0 50.0 50.0 50.0 50.0 50.0 50.0 50.0\r\n");
	            else if(strncmp(tmp,"RDN",3) == 0)  /** RDN property **/    	
			strcat(nio_TXbuff, " 100.0 100.0 100.0 100.0 100.0 100.0 100.0 100.0 100.0 100.0 100.0 100.0\r\n");
	            else if(strncmp(tmp,"ST",2) == 0)  /** ST property **/    	
			strcat(nio_TXbuff, " 01 00 00 00 00 00 00 00 00 00 00 00\r\n");
	            else if(strncmp(tmp,"MVDZ",4) == 0)  /** MVDZ property **/    	
			strcat(nio_TXbuff, " 5.0 5.0 5.0 5.0 5.0 5.0 5.0 5.0 5.0 5.0 5.0 5.0\r\n");
	            else if(strncmp(tmp,"MCDZ",4) == 0)  /** MCDZ property **/    	
			strcat(nio_TXbuff, " 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0\r\n");
	            else if(strncmp(tmp,"TC",2) == 0)  /** TC property **/    	
			strcat(nio_TXbuff, " 13.0 13.0 13.0 13.0 13.0 13.0 13.0 13.0 13.0 13.0 13.0 13.0\r\n");
	            else if(strncmp(tmp,"HVL",3) == 0)  /** HVL property **/    	
			strcat(nio_TXbuff, " -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0 -2500.0\r\n");
	            else if(strncmp(tmp,"MV",2) == 0)  /** MV property **/    	
			strcat(nio_TXbuff, " 4.3 0.3 0.3 0.3 0.3 0.3 0.3 0.3 0.3 0.3 0.3 0.3\r\n");
	            else if(strncmp(tmp,"MC",2) == 0)  /** MC property **/    	
			strcat(nio_TXbuff, " 0.1 0.1 0.1 0.1 0.1 0.1 0.1 0.1 0.1 0.1 0.1 0.1\r\n");


		   else strcat(nio_TXbuff, " 0 0 0 0 0 0 0 0 0 0 0 0\r\n");
		}
	

/*		else strcpy(nio_TXbuff, "1 RC DV 0 0 0 0 0 0 0 0 0 0 0 0\r\n");*/
		else strcpy(nio_TXbuff, nio_RXbuff); /* sent back incomming command */

/*** 		strcat(nio_TXbuff, nio_RXbuff);
		strcpy(nio_TXbuff, nio_RXbuff); **/

		nio_TXlen = strlen(nio_TXbuff);
	   printf(" cmdTsk: strncmp() got %s\n",nio_RXbuff);
	}
	else {
/*	  printf(" cmdTsk: got %s\n",nio_RXbuff); */
	  if(cmdEXE() != NORMAL) /* command execution had an error */
          {
          nio_TXbuff[0] = '\0';
          strcpy(nio_TXbuff,"?\r\n");
          nio_TXlen = strlen(nio_TXbuff);
          }
/*	  else printf(" cmdTsk: cmdEXE() returns NORMAL: %s\n", nio_TXbuff);*/
	}
	
/**** 12-May-2014 ****/	
	if(0) {
	if(cmdEXE() != NORMAL) /* command execution had an error */
        {
        nio_TXbuff[0] = '\0';
        strcpy(nio_TXbuff,"?\r\n");
        nio_TXlen = strlen(nio_TXbuff);
        }
       }/*if(0)*/

      /* received command to quit - bail out of this loop */
      if(nio_quit)
	    {
	    printf("cmdTSK : quit\n");
	    nio_quit = 0;
	    return;
	    }

	  /* send replay back */
	  /* add prompt */
	  strcat(nio_TXbuff, prompt);
	  nio_TXlen = strlen(nio_TXbuff);
	  if(send(connection_fd, nio_TXbuff, nio_TXlen, 0) < 0)
	    {
		printf("cmdTSK - error sending message....\n");
		}
	  time(&now); 
	  printf(" %s ", ctime(&now));	  
          printf("cmdTSK : sentback: %s\n", nio_TXbuff);
	
	}
	}

	printf("cmdTSK - exit loop....\n");
  }



/* ======================================================================================
 *
 * Network Server
 *
 * ======================================================================================
 */
static void NetServer(unsigned short port)
  {
  pid_t child_pid;
  int mySock, connection, yes=1;
  struct sockaddr_in myAddr, remAddr;
  socklen_t addrlen;

  /* Create socket */
  mySock = socket (AF_INET, SOCK_STREAM, 0);
  if(mySock < 0)
    {
    printf("NetServer - Can't create socket ...\n");
    exit(1);
    }
  
  /* Allow socket address reuse */
  if(setsockopt(mySock, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(int)) == -1)
    {
    printf("NetServer - Setsockopt error .....");
    exit(1);
    }
 
  /* Bind socket */
  memset(&myAddr, 0, sizeof(myAddr));
  myAddr.sin_family = AF_INET;
  myAddr.sin_port = htons (port);
  myAddr.sin_addr.s_addr = INADDR_ANY;
  if(bind(mySock, (struct sockaddr *)&myAddr, sizeof(myAddr)) != 0)
	{
	printf("NetServer - Can't bind to socket: %s", strerror (errno));
	exit(1);
	}
		
  /* Listen for connections */
  if(listen(mySock, 10) < 0) /* maximum of 10 pending connections */
    {
    printf("NetServer - Can't listen on socket: %s", strerror (errno));
    exit(1);
    }
		
  /* Accept connection */		
  for(;;)
    {
	addrlen = sizeof(remAddr);
	connection = accept(mySock, (struct sockaddr *)&remAddr, &addrlen);
	if(connection < 0)
	  {
	  printf("NetServer - Can't accept new connection: %s", strerror(errno));
	  exit(1);
	  }
	/* else
	  {
	  printf ("ACCEPTED:%lX\n", ntohl (farAddr.sin_addr.s_addr));
	  }
	 */
	  
    /* fork a child process to handle connection */
	child_pid = fork();
	if(child_pid == 0)
	  {
	  /* this is the child process.
	   * the listeing socket is not needed by this process - close it
	   */
	  close(mySock);
	
      /* Handle requests coming throught the connection - the child has a copy of the
         connected socket descriptor */
	  cmdTSK(connection);
	  
	  /* if we are here - all it is done: close the connection socket and end the child process */
	  close(connection);
	  exit(0);
	  }
	else
	  {
	  if(child_pid > 0)
	    {
		/* this is the parent process. The child process handles the connection
		 * so we can close this copy of the
		 * socket descriptor. The parent then continues with the loop over connections and
		 * accepts a new connection ..
		 */
	    close(connection);
		}
	  else
		{
		/* failed to fork child process */
		printf("NetServer - Failed to fork child process to handle new connection: %s", strerror(errno));
		exit(0);
		}
	  }
	}
  }



/* ======================================================================================
 *
 *  Ethernet to LeCroy HV modules Bridge via a Raspberry Pi (rPI)
 *
 * =======================================================================================
 */
int main(void)
  {
  char LU_type[nLUTYP][L16] = {"1461PS0", "1461NS0", "1469PS0", "1469PS1",
  "1469NS0", "1469NS1", "1471PS0", "1471NS0"};
   
  unsigned char ga, tbuff[L256], rbuff[L256], s1[L256], s2[L256], s3[L256], sdum[L256], *ps1;
  int imod, slot, nsm, sm, i1, i2, i3, i4;
  
  int fd;

  /*initialize */
  for(i1 = 0; i1 < nLU; i1++) pLU[i1] = NULL;
  for(i1 = 0; i1 < nSLOTS; i1++)
    {
    /* negaitve # indicates empty slot/submodule */
    for(i2 = 0; i2 < nSUBMOD; i2++) SS2LU[i1][i2] = -1;
    }
 
  /* Setup rPI serial to communicate with the HV modules
   * Options:
   *	O_RDWR: read & write access to port
   *    O_CTTY: prevent other input (e.g. keyboard) from affecting what we read
   *    O_NONBLOCK: do not block waiting for a response
   * MAPPING REQUIRES ROOT PRIVILIGES OR CHANGING ACCESS PREVILIGES OF /dev/ttyUSB0 
   */
  sio = open ("/dev/ttyAMA0", O_RDWR | O_NOCTTY | O_NDELAY);
  if(sio < 0)
    {
    printf("Unable to open /dev/ttyAMA0 ....\n");
    exit(-1);
    }
  bzero(&sio_attr, sizeof(sio_attr));
  sio_attr.c_iflag = IGNBRK | IGNPAR;
  sio_attr.c_oflag = 0; /* output mode flags  - raw output */
  /* 38400 baud, 8-bits, no parity, 1-stop bit,
   * no xonxoff, no rtscts
   */
  sio_attr.c_cflag = B38400 | CS8 | CREAD | CLOCAL;  /* control mode flags */
  sio_attr.c_lflag = 0; /* local mode flags */
  sio_attr.c_cc[VTIME]= 0; /* read - inter-character timer unused */
  sio_attr.c_cc[VMIN] = 0; /* read - minimum number of characters */
  
  tcflush (sio,TCIFLUSH);
  tcsetattr (sio, TCSANOW, &sio_attr);
	  
  /* ATTN* signal from HV module is routed to GPIO23
   * Setup system to access GPIO registers
   * Access GPIO23 as input, no interrupt, pull/down disabled (all are defaults)
   * MAPPING REQUIRES ROOT PRIVILIGES OR CHANGING ACCESS PREVILIGES OF /dev/mem 
   */   
   fd = open("/dev/mem", O_RDWR | O_SYNC); /* needs to run as root!! */
   if(fd < 0)
     {
     printf("Unable to open /dev/mem ....\n");
     exit(-1);
     }

   gpioReg = mmap
      (
      0,
      0xB4,     /* length of GPIO registers */
      PROT_READ|PROT_WRITE|PROT_EXEC,
      MAP_SHARED|MAP_LOCKED,
      fd,
      0x20200000); /* beginning of GPIO registers in memory */

   close(fd);

  
  /* Send handshake message to every slot to determine which ones have a module.
   * This will also clear any module holding the ATTN* line (it has a pending response
   * in its output buffer)
   */
  for(slot = 0; slot < nSLOTS; slot++)
    {
	ga = 255 - slot;  /* geographical address of slot */
	sio_TXbuff[0] = ga;
	sio_TXbuff[1] = 0x06;  /* ACK */
	sio_TXbuff[2] = '\n';
	sio_TXbuff[3] = '\0';
	write(sio,sio_TXbuff,strlen(sio_TXbuff));	
	if(msgget(50) > MSGstat_NONE) SLOTwMOD[nMOD++] = slot; /* 50 char wait */
	}	  	
  if(nMOD <= 0)
    {
/*** 01-May-2014 
   printf("i2lchv - no modules found.... exiting\n");
    exit(0);
***/
    }

if(1) {	  
  /* get module ID */
  for(imod = 0; imod < nMOD; imod++)
    {
    /* retrieve slot# of module */
    slot = SLOTwMOD[imod];
    /* get number of submodules in this module */
    ga = 255 - slot;
	sio_TXbuff[0] = ga;
	sio_TXbuff[1] = 0x06;
	sio_TXbuff[2] = '\0';
    /* Note: we choose to use the slot# as the transation ticket# */
    sprintf(s1,"%d SM\n",slot);
    strcat(sio_TXbuff,s1);
    sio_TXlen = strlen(sio_TXbuff);
	write(sio,sio_TXbuff,sio_TXlen); /* send message */
	if(msgget(sio_TXlen+50) != MSGstat_HNDSHK) goto skip_slot; /* get handshake */
    
    /* wait up-to 2 sec for module to indicate is ready to send response to previous command */
    if(IsGpioSet(23,2.0) != NORMAL) goto skip_slot;
      
    /* Module has response ready - send handshake sequence to start xfer
     * The slot geographical address & 0x06 (ACK) are
     * already in the buffer - we just add the LF and a NULL
     */
    sio_TXbuff[2] = '\n';
    sio_TXbuff[3] = '\0';
    sio_TXlen = strlen(sio_TXbuff);
    write(sio,sio_TXbuff,strlen(sio_TXbuff)); /* send handshake */            
    if(msgget(50) != MSGstat_OK) goto skip_slot; /* 50 char wait (13ms) */

    /* decode message */
    sio_MSGbuff[sio_MSGlen] = '\0';        
    sio_MSGbuff[0] = ' '; /* convert ACK char into SPACE for decoding */
    
    /* message terminates with CRLF */
    ps1 = strchr(sio_MSGbuff,'\r');   /* search for CR */
    *ps1 = '\0';       /* replace CR by NULL to terminate string */
    sscanf(sio_MSGbuff,"%d %s %d",&i1,s1,&nsm);
      
    /* Check that the ticket-number field matches the slot# (we sent this value)
     * & the command is "SM"
     */
    if((i1 != slot) || (strcmp(s1,"SM") != 0)) goto skip_slot; /* error */
    
    /* get module ID & submodule information (e.g number of channels & properties) */
    for(i3 = 0;  i3 < nsm;  i3++)
      {
      sio_TXbuff[2] = '\0';
      if(nsm <= 1)
        {
        /* one sub-module, commands do not include sub-module address
         * Use the slot# as the transation ticket#
         */
        sprintf(s1,"%d ID\n",slot);
        }
      else
        {
        /* sub-module i3 of [ 0 -> (nsm-1)]
         * Use the slot# as the transation ticket#
         */
        sprintf(s1,"%d %d ID\n",slot,i3);
        }
      strcat(sio_TXbuff,s1);
      sio_TXlen = strlen(sio_TXbuff);
      write(sio,sio_TXbuff,sio_TXlen); /* send command */
	  if(msgget(sio_TXlen+50) != MSGstat_HNDSHK) goto skip_submodule; /* get handshake */
              
      /* wait up-to 2 sec for module to indicate is ready to send response to previous command */
      if(IsGpioSet(23,2.0) != NORMAL) goto skip_submodule;
      
      /* module ready - send handshake sequence to start xfer
       * The slot geographical address & 0x06 (ACK) are
       * already in the buffer - we just add the LF and a NULL
       */
      sio_TXbuff[2] = '\n';
      sio_TXbuff[3] = '\0';
      sio_TXlen = strlen(sio_TXbuff);
      write(sio,sio_TXbuff,sio_TXlen);           
      if(msgget(50) != MSGstat_OK) goto skip_submodule; /* 50 char wait (13ms) */

      /* decode response  - response should start with "YXX ID " where Y = 0x06 &
       * XX = transation ticket# = slot# (one or 2 characters)      
       * Skip over the number of bytes taken by preamble (ACK, slot# & command) */
      i1 = 1;
      if(slot > 9) i1 = 2;
      i1 = i1+5; /* 5 bytes = ACK + " ID " */
      strcpy(s1,&sio_MSGbuff[i1]);
      
      ps1 = strchr(s1,'\r');  /* end-of-message sequence is CRLF. Search for CR */
      *ps1 = '\0';  /* replace CR by NULL to terminate string */
      sscanf(s1,"%s",s2);  /* s2 should be the module type */
      sprintf(s3,"S%d",i3);  /*submodule number */
      strcat(s2,s3);    /* logic unit type  */
                  
      /* search for logic unit type */
      i2 = -1;
      for(i1 = 0; i1 < nLUTYP; i1++)
        {
        i4 = strcmp(&LU_type[i1][0],s2);
        if(i4 == 0) i2 = i1;
        }
                   
      /* skip if no matching logic unit found */
      if(i2 < 0)
        {
        printf("main - unknown logic unit type %s @ slot = %d\n",s2,slot);
        goto skip_submodule;
        }
      
      /* found logic unit type */ 
      /* create structure to store this logic unit info */
      pLUtmp = NULL;
      pLUtmp = (struct LUnit *)malloc(sizeof(struct LUnit));
      
      if(pLUtmp == NULL) /* failed to allocate structure */
        {
        printf("main - malloc failed!, slot = %d, smod = %d, LUTYP = %s\n\n",slot,i3,s2);
        goto skip_submodule;
        }
      lstLU = lstLU +1;
      pLU[lstLU] = pLUtmp;
                      
      /* store - basic header for commands */
      pLUtmp->hdr[0] = ga;
      pLUtmp->hdr[1] = 0x06;
      pLUtmp->hdr[2] = '\0';
      if(nsm <= 1)
        {
        /* One sub-module, commands do not include sub-module address
         * The slot# is used as the transaction#
         */
        sprintf(s3,"%d ",slot);
        }
      else
        {
        /*sub-module i3 of [ 0 -> (nsm-1)]
         * The slot# is used as the transaction#
         */
        sprintf(s3,"%d %d ",slot,i3);
        }
      strcat(pLUtmp->hdr,s3);
                      
      /* store - ack message */
      pLUtmp->ack[0] = ga;
      pLUtmp->ack[1] = 0x06;
      pLUtmp->ack[2] = '\n';
      pLUtmp->ack[3] = '\0';
                      
      /* store - */
      pLUtmp->lutype = i2; /* logic unit type index */
      pLUtmp->slot = slot; /* slot number */
      pLUtmp->nsmod = nsm;   /* number of submodules */
      pLUtmp->smod = i3; /* submodule number */
      strcpy(pLUtmp->id,s1); /* module/submodule id */
                      
      /* Map Slot/submodule to LU */
      SS2LU[slot][i3] = lstLU;
        
      skip_submodule: continue;
      } /* bottom of loop over submodules */
    
    skip_slot: continue;
    } /* bottom over slots */
 } /* if(0)*/
   
  /* Telnet server */
  printf("Network server started\n");	
  NetServer(BASE_PORT);
  };

