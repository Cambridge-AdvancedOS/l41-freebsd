/*
 *	    Written by Toshiharu OHNO (tony-o@iij.ad.jp)
 *
 *   Copyright (C) 1993, Internet Initiative Japan, Inc. All rights reserverd.
 *
 * Redistribution and use in source and binary forms are permitted
 * provided that the above copyright notice and this paragraph are
 * duplicated in all such forms and that any documentation,
 * advertising materials, and other materials related to such
 * distribution and use acknowledge that the software was developed
 * by the Internet Initiative Japan.  The name of the
 * IIJ may not be used to endorse or promote products derived
 * from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED
 * WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.
 *
 * $Id: modem.h,v 1.16.2.1 1998/01/29 00:49:27 brian Exp $
 *
 *	TODO:
 */

struct physical;

extern int RawModem(struct physical *);
extern int OpenModem(struct physical *);
extern int ModemSpeed(struct physical *);
extern int DialModem(struct physical *);
extern speed_t IntToSpeed(int);
extern void ModemTimeout(void *);
extern void DownConnection(void);
extern int ChangeParity(struct physical *, const char *);
extern int ShowModemStatus(struct cmdargs const *);
extern int ReportProtocolStatus(struct cmdargs const *arg);
