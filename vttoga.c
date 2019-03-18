//
//  Copyright (c) 2010 Paul Nicholson
//  All rights reserved.
//  
//  Redistribution and use in source and binary forms, with or without
//  modification, are permitted provided that the following conditions
//  are met:
//  1. Redistributions of source code must retain the above copyright
//     notice, this list of conditions and the following disclaimer.
//  2. Redistributions in binary form must reproduce the above copyright
//     notice, this list of conditions and the following disclaimer in the
//     documentation and/or other materials provided with the distribution.
//  
//  THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
//  IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
//  OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
//  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
//  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
//  NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
//  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
//  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
//  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
//  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//

#include "config.h"
#include "vtport.h"
#include "vtlib.h"

#include <fftw3.h>

// Important times, all in seconds
static double Tbuf = 0.06;                 // Buffer length
static double Tpulse = 0.0015;             // Pulse length analysed
static double Tfft = 0.006;                // FFT input width
static double Tpretrig =  200e-6;          // Pre-trigger period
static double Thold = 0.002;               // Re-trigger hold-off period

// Set by command line options
static int EFLAG = 0;                  // Non-zero if -e given, output spectrum
static int RFLAG = 0;                   // Non-zero if -r given, auto threshold
static int CFLAG = 0;                 // Non-zero if -c given, calibration mode

static int Nmax = 0;             // From -N option: number of pulses to capture
static double throttle = 0;      // From -r option: target rate triggers/second
static double Etime = 0;            // From -E option, stop after Etime seconds
static int gran = 3600;              // From -G option: output file granularity
static char *outdir = NULL;                 // From -d option: output directory
static timestamp Ttrig;             // From -T option: single shot trigger time
static double qfactor = 0;                 // From -q option: quality threshold

// Variables for auto threshold
static time_t last_T = 0;               // Start time for trigger rate counting
static int last_N = 0;                       // Number of triggers since last_T
#define AT_INT 10                   // Seconds between updates of trigger level

// Limits for accepting a measurement
static double limit_corr = 0.9;   // Set by option -f corr= 
static double limit_phres = 1.5;  // Set by option -f phres=
static double limit_ascore = 5.0; // Set by option -f ascore

static double trigger_level = 0;                    // Trigger level, set by -h 
static timestamp Tstart = timestamp_ZERO;          // Timestamp of first sample 
static complex double *XX;

static struct CHAN
{
   double *buf;                                        // Circular input buffer
   double *fft;                                             // FFT input buffer
   complex double *X;                                             // FFT output
   double rms;                                        // RMS amplitude of pulse
   fftw_plan fp;
} *channels;

static int chans = 0;
static int sample_rate = 0;

static int buflen = 0;                       // Circular buffer length, samples
static int btrig = 0;                            // Pre-trigger period, samples
static int bp = 0;                         // Base pointer into circular buffer
static int FFTWID = 0;                                    // FFT width, samples
static int BINS = 0;                                          // Number of bins
static double DF = 0;                                   // Frequency resolution
static double DT = 0;                                        // Time resolution
static double F1 = 4000, F2 = 17000;              // Frequency range to analyse
static int bf1, bf2;            // Start and finish bin numbers, from F1 and F2
static timestamp Tin;                        // Timestamp of most recent sample
static int thold = 0;                       // Trigger hold-off period, samples
static int one_shot = 0;                                // Non-zero if -T given
static int N_out = 0;                      // Number of sferics processed

//  Variables for polar operation
static int polar_mode = 0;
static double polar1_align = 0;        // Azimuth of 1st H-loop channel
static double polar2_align = 0;        // Azimuth of 2nd H-loop channel

static int ch_EFIELD = -1;
static int ch_HFIELD1 = -1;
static int ch_HFIELD2 = -1;

#define BUF(C,P) channels[C].buf[((P) + bp + buflen) % buflen]

#define DEFAULT_THRESHOLD 0.1   // Trigger threshold, rate of change per sample
#define EIC_CUTOFF 1700
#define EARTH_RAD 6371.0
#define C 299.792e3

static void usage( void)
{
   fprintf( stderr,
       "usage:  vttoga [options] [input]\n"
       "\n"
       "options:\n"
       "  -v            Increase verbosity\n"
       "  -B            Run in background\n"
       "  -L name       Specify logfile\n"
       "  -F start,end  Frequency range (default 4000,17000)\n"
       "  -E seconds    Stop after so many seconds\n"
       "  -h thresh     Trigger threshold (default %.1f)\n"
       "  -r rate       Auto threshold to this rate/second\n"
       "  -e            Spectrum and waveform data for each sferic\n"
       "  -d outdir     Output directory (defaults to stdout)\n"
       "  -G seconds    Output file granularity (default 3600)\n"
       "  -T timestamp  One-shot trigger time\n"
       "  -c            Calibration mode\n"
       "  -p polarspec  Specify orientation of input channels\n"
       "  -N count      Examine this many sferics then exit\n",
      DEFAULT_THRESHOLD);
   exit( 1);
}

static double vf( double f1, double f2, double fc)
{
   double wc = fc * 2 * M_PI;
   double w1 = f1 * 2 * M_PI;
   double w2 = f2 * 2 * M_PI;

   double w1_2 = w1*w1;
   double w1_3 = w1*w1*w1;

   double w2_2 = w2*w2;
   double w2_3 = w2*w2*w2;

   double wc_2 = wc*wc;

   double F1 = log( (1+sqrt(1-wc_2/w1_2))*(1 - sqrt(1-wc_2/w2_2)) /
                    ((1+sqrt(1-wc_2/w2_2))*(1 - sqrt(1-wc_2/w1_2))) );

   double G1 = sqrt((w1-wc)*(wc+w1));
   double G2 = sqrt((w2-wc)*(wc+w2));

   double H1 = 8*wc_2 + 6*w1*w2  - 2*w1_2;
   double H2 = 8*wc_2 + 6*w1*w2  - 2*w2_2;

   double vf = -2 * (w2_3-3*w1*w2_2+3*w1_2*w2-w1_3) /
              (3*(w2+w1)*wc_2*F1 + G2*H2 - G1*H1);

//   double wz = wc/sqrt(1 - vf*vf);
//   printf( "least squares %.6f %.2f\n", vf, wz/(2 * M_PI));

   return vf;
}

struct EVENT {
   double range;
   double phresidual;
   double toga_offset;             // Seconds between Tf and toga
   timestamp Tf;                   // Timestamp of first sample of buffer
   timestamp toga;
   double rms;
   double bearing;
   double *upb;                    // Unwrapped phase, radians
   double *tsp;                    // Phase at the TOGA, radians
   double *dphi;                   // d(phase)/d(omega), seconds
   double *csp;                    // Model phase at the TOGA, radians
   int *mask;                      // Bin mask, TRUE = exclude phase bin
   double ts_icept;
   double ts_slope;
   double corr;
   double used;
   double ascore;
};

static void init_event( struct EVENT *ev)
{
   memset( ev, 0, sizeof( struct EVENT));
   ev->upb = VT_malloc_zero( sizeof( double) * BINS);
   ev->tsp = VT_malloc_zero( sizeof( double) * BINS);
   ev->csp = VT_malloc_zero( sizeof( double) * BINS);
   ev->dphi = VT_malloc_zero( sizeof( double) * BINS);
   ev->mask = VT_malloc_zero( sizeof( int) * BINS);
}

static void free_event( struct EVENT *ev)
{
   free( ev->upb);
   free( ev->tsp);
   free( ev->csp);
   free( ev->dphi);
   free( ev->mask);
}

///////////////////////////////////////////////////////////////////////////////
//  Output Functions                                                         //
///////////////////////////////////////////////////////////////////////////////

//
//  Output a 'H' record - timestamp and total amplitude.
//

static void output_standard( FILE *f, struct EVENT *ev)
{
   char temp[30];

   timestamp_string6( ev->toga, temp);
   fprintf( f, "H %s %.3e %.0f %.2f %.2f %.2f",
               temp,               // Timestamp, 1uS resolution
               ev->rms,
               ev->range,
               ev->phresidual,
               ev->corr,
               ev->ascore);

   if( polar_mode) fprintf( f, " %.1f", ev->bearing * 180/M_PI);

   fprintf( f, "\n");
}

//
// Extended output records if -e is given.  
//    H is the header record, call output_standard() for that;
//    S records for spectrum data;
//    T records for time domain;
//    E is an end marking record;
//

static void output_extended( FILE *fo, struct EVENT *ev)
{
   int ch, j;

   for( j = bf1; j <= bf2; j++)
   {
      double f = j * DF;
      double fc = 1670;
      double x = 1/sqrt( 1 - fc*fc/(f*f));
   
      fprintf( fo, "S %.3f %.3e %.2f %.2f %.4e %.4e %.4e %d %.3e\n",
           f,                 // Frequency, Hz
           cabs(XX[j]),       // Bin amplitude
           ev->upb[j] * 180/M_PI, // Unwrapped phase, degrees
           ev->tsp[j] * 180/M_PI, // Phase at TOGA, degrees
           x,                 //
           ev->dphi[j],       // d(tsp)/d(omega)
           ev->ts_icept + x * ev->ts_slope,
           ev->mask[j],
           ev->csp[j] * 180/M_PI);         
   }
   for( j = 0; j < Tpulse * sample_rate; j++)
   {
      fprintf( fo, "T %.6e", j * DT + ev->toga_offset);
      for( ch = 0; ch < chans; ch++) fprintf( fo, " %.4e", BUF(ch, j));
      fprintf( fo, "\n");
   }

   fprintf( fo, "E\n");
}

static void output_record( struct EVENT *ev)
{
   //
   // Open an output file if -d given, otherwise use stdout.
   //

   FILE *f;

   if( !outdir) f = stdout;
   else
   {
      char *filename;
      time_t secs = timestamp_secs( timestamp_add( Tin, -buflen * DT));
      secs = (secs / gran) * gran;
      struct tm *tm = gmtime( &secs);

      if( asprintf( &filename, "%s/%02d%02d%02d-%02d%02d%02d",
            outdir,
            tm->tm_year % 100, tm->tm_mon + 1, tm->tm_mday,
            tm->tm_hour, tm->tm_min, tm->tm_sec) < 0)
         VT_bailout( "out of memory");
      if( (f = fopen( filename, "a")) == NULL)
         VT_bailout( "cannot open %s: %s", filename, strerror( errno));
      free( filename);
   }

   output_standard( f, ev);
   if( EFLAG) output_extended( f, ev);

   if( f != stdout) fclose( f);
}

///////////////////////////////////////////////////////////////////////////////
//  Sferic Analyser                                                          //
///////////////////////////////////////////////////////////////////////////////

static int cmp_double( const void *p1, const void *p2)
{
   double v1 = *(double *)p1;
   double v2 = *(double *)p2;

   if( v1 < v2) return -1;
   if( v1 > v2) return 1;
   return 0;
}

static int compute_event( struct EVENT *ev)
{
   int i, j, k;

   //
   //  Make a list of un-masked bins.
   //

   int list[500];
   int nlist = 0;
   list[0] = 0;
   for( j = bf1; j <= bf2; j++)
      if( !ev->mask[j]) list[nlist++] = j;
   if( !nlist) return FALSE;

   //
   //  Unwrap the bin phases into ev->upb[].
   //  Skip over any bins that are masked.
   //

#if 0
   double b = 0;
   for( j = bf1; j <= bf2; j++) if( !ev->mask[j]) break;
   ev->upb[j] = b;

   while( j < bf2)
   {
      if( ev->mask[j]) { j++; continue; }

      for( k = j+1; k <= bf2; k++) if( !ev->mask[k]) break;
      if( k > bf2) break;

      double dp = carg( XX[k]) - carg( XX[j]);
      while( dp > 0) dp -= 2*M_PI;
      while( dp < -M_PI) dp += 2*M_PI;
      b += dp;
      ev->upb[k] = b;
      j = k;
   }
#endif

   double b = 0;
   ev->upb[list[0]] = b;
   for( i = 0; i < nlist-1; i++)
   {
      j = list[i];  k = list[i+1];
      double dp = carg( XX[k]) - carg( XX[j]);
      while( dp > 0) dp -= 2*M_PI;
      while( dp < -M_PI) dp += 2*M_PI;
      b += dp;
      ev->upb[k] = b;
   }
  
   //
   //  Least squares regression to find the average phase slope.
   //

   double fsum = 0;
   double psum = 0;

   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      fsum += j * DF;
      psum += ev->upb[j];
   }

   double fmean = fsum / nlist;
   double pmean = psum / nlist;

   double num = 0;
   double denom = 0;

   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      double d = j * DF - fmean;
      num += d * (ev->upb[j] - pmean);
      denom += d * d;
   }
   double alpha = pmean - num/denom * fmean; // Radians

   ev->toga_offset = num/(denom * 2 * M_PI); // Cycles per Hz = seconds
   if( ev->toga_offset >= 0) return FALSE;

   ev->toga = timestamp_add( ev->Tf, -ev->toga_offset);

   //
   //  Rotate the unwrapped phase ev->upb[], time shifting to the TOGA.
   //

   for( j=bf1; j<=bf2; j++)
      ev->tsp[j] = ev->upb[j] - (alpha + j * 2 * M_PI * DF * ev->toga_offset);

   //
   //  Phase slope at the TOGA, d(phase)/d(omega).
   //

   memset( ev->dphi, 0, sizeof( double) * BINS);
   double dw = 2 * M_PI * DF;
   for( i = 0; i < nlist; i++)
   {
      if( i < nlist-1)
      {
         j = list[i];  k = list[i+1];
         ev->dphi[j] = (ev->tsp[k] - ev->tsp[j])/(dw * (k - j));
      }
      else
      if( i > 0)
      {
         j = list[i];  k = list[i-1];
         ev->dphi[j] = (ev->tsp[j] - ev->tsp[k])/(dw * (j - k));
      }
   }

   //
   //  Slope of dphi[] against 1/sqrt( 1 - wc^2/w^2) by Theil-Sen regression.
   //

   int nb = bf2 - bf1 + 1;
   double *tsbuf = VT_malloc_zero( sizeof( double) * nb * (nb-1)/2);

   int nts = 0;
   double wc = 1670 * 2 * M_PI;

   for( j = 0; j < nlist; j++)
      for( k = j+1; k < nlist; k++)
      {
         double wj = list[j] * DF * 2 * M_PI;
         double wk = list[k] * DF * 2 * M_PI;

         double xj = 1/sqrt( 1 - wc*wc/wj/wj);
         double xk = 1/sqrt( 1 - wc*wc/wk/wk);

         tsbuf[nts++] = (ev->dphi[list[k]] - ev->dphi[list[j]])/(xk - xj);
      }
      
   qsort( tsbuf, nts, sizeof( double), cmp_double);

   ev->ts_slope = tsbuf[nts/2];  // Radians per step
   free( tsbuf);

   ev->range = -ev->ts_slope * C;
   if( ev->range <= 0) return FALSE;

   double ts_sum = 0;
   int ts_sumn = 0;

   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      double w = j * DF * 2 * M_PI;
      double wc = 1670 * 2 * M_PI;

      double x = 1/sqrt( 1 - wc*wc/w/w);
      ts_sum += ev->dphi[j] - ev->ts_slope * x;
      ts_sumn++;
   } 

   ev->ts_icept = ts_sum / ts_sumn;

   //
   //  Construct a model sferic based on the estimated range, putting its
   //  phase into ev->csp[].
   //

   double vg = C * vf( F1, F2, 1670);
   for( j = bf1; j <= bf2; j++)
   {
      double w = 2 * M_PI * DF * j;
      double wc = 2 * M_PI * 1670;
      ev->csp[j] = ev->range * w/vg - ev->range * w/C * sqrt(1 - wc*wc/(w*w));
   }

   double h = 0;
   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      h += ev->csp[j] - ev->tsp[j];
   }  
   for( j = bf1; j <= bf2; j++) ev->csp[j] -= h/nlist;

   //
   //  RMS residual between modeled and measured phase.
   //

   double rs = 0;
   for( i = 0; i < nlist; i++)
      {
         j = list[i];
         double d = ev->csp[j] - ev->tsp[j];
         rs += d * d;
      }
   ev->phresidual = sqrt(rs/nlist);  // Radians

   //
   //  Weighted correlation coefficient between csp[] and tsp[].
   //

   double sumx = 0, sumy = 0, sumw = 0;
   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      sumw += cabs( XX[j]);
      sumx += cabs( XX[j]) * ev->tsp[j];
      sumy += cabs( XX[j]) * ev->csp[j];
   }
   double mx = sumx/sumw;
   double my = sumy/sumw;

   double sum_xy = 0, sum_xx = 0, sum_yy = 0;
   for( i = 0; i < nlist; i++)
   {
      j = list[i];
      sum_xy += cabs( XX[j]) * (ev->tsp[j] - mx) * (ev->csp[j] - my);
      sum_xx += cabs( XX[j]) * (ev->tsp[j] - mx) * (ev->tsp[j] - mx);
      sum_yy += cabs( XX[j]) * (ev->csp[j] - my) * (ev->csp[j] - my);
   }

   double covxy  = sum_xy / sumw;
   double covxx  = sum_xx / sumw;
   double covyy  = sum_yy / sumw;

   ev->corr = covxy/sqrt( covxx * covyy);

   //
   //  Amplitude spectrum score.
   //

   double pkmax = 0;
   
   for( i = 0; i < nlist; i++)
   {
      double a = cabs( XX[list[i]]);

      if( a > pkmax) pkmax = a;
   }

   double last_a = cabs( XX[0]);
   double asum = 0;

   for( i = 1; i < nlist-1; i++)
   {
      double d1 = cabs( XX[list[i]]) - cabs( XX[list[i-1]]);
      double d2 = cabs( XX[list[i]]) - cabs( XX[list[i+1]]);
     
      if( d1 < 0 && d2 > 0) continue;
      if( d1 > 0 && d2 < 0) continue;

      asum += fabs( cabs( XX[list[i]]) - last_a);
      
      last_a = cabs( XX[list[i]]);
   }
   asum += fabs( cabs( XX[list[nlist-1]]) - last_a);

   ev->ascore = asum / pkmax;
   return TRUE;
}

static void compute_bearing( struct EVENT *ev)
{
   int j;

   if( polar_mode)
   {
      // Matrix to correct for the loop alignments
      double cos1 = cos( polar1_align);
      double cos2 = cos( polar2_align);
      double sin1 = sin( polar1_align);
      double sin2 = sin( polar2_align);
      double det = sin1*cos2 - cos1*sin2;

      double bsin = 0;
      double bcos = 0;

      //
      // Calculate the bearing for each frequency bin and do an average
      // weighted by the RMS amplitude.
      //
      for( j=bf1; j<=bf2; j++)
      {
         if( ev->mask[j]) continue;

         complex double *H1 = channels[ch_HFIELD1].X;
         complex double *H2 = channels[ch_HFIELD2].X;

         // N/S and E/W signals, correcting for loop azimuths
         complex double ew = (cos2 * H1[j] - cos1 * H2[j]) * det;
         complex double ns = (-sin2 * H1[j] + sin1 * H2[j]) * det;

         double mag_ew = cabs( ew);
         double mag_ns = cabs( ns);
         double pow_ew = mag_ew * mag_ew;
         double pow_ns = mag_ns * mag_ns;

         // Phase angle between N/S and E/W
         double phsin = cimag( ns) * creal( ew) - creal( ns) * cimag( ew);
         double phcos = creal( ns) * creal( ew) + cimag( ns) * cimag( ew);
         double a = atan2( phsin, phcos);

         // Watson-Watt goniometry to produce cos and sine of 2*bearing.
         double bearing2sin = 2 * mag_ew * mag_ns * cos( a);
         double bearing2cos = pow_ns - pow_ew;
         double pwr = pow_ew + pow_ns;

         double weight = pwr;

         if( ch_EFIELD < 0)
         {
            // No E-field available, so average the sin,cos of 2*bearing
            bsin += bearing2sin * weight;
            bcos += bearing2cos * weight;
            continue;
         }

         // E-field available, compare phase of E with H 
         double bearing180 = atan2( bearing2sin, bearing2cos)/2;
         if( bearing180 < 0) bearing180 += M_PI;
         else
         if( bearing180 >= M_PI) bearing180 -= M_PI;

         //  H-field signal in plane of incidence
         complex double or = ew * sin( bearing180) +
                             ns * cos( bearing180);

         complex double vr = channels[ch_EFIELD].X[j];

         // Phase angle between E and H
         double pha =
              atan2( cimag( or) * creal( vr) - creal( or) * cimag( vr),
                     creal( or) * creal( vr) + cimag( or) * cimag( vr));

         // Reflect the mod 180 bearing to the correct quadrant
         double bearing360 = bearing180;
         if( pha < -M_PI/2 || pha > M_PI/2) bearing360 += M_PI;

         // Average the sin,cos of the bearing
         bsin += sin( bearing360) * weight;
         bcos += cos( bearing360) * weight;
      }

      if( ch_EFIELD < 0) // Bearing modulo 180
      {
         ev->bearing = atan2( bsin, bcos)/2;
         if( ev->bearing < 0) ev->bearing += M_PI;
      }
      else  // Bearing modulo 360
      {
         ev->bearing = atan2( bsin, bcos);
         if( ev->bearing < 0) ev->bearing += 2 * M_PI;
      }

      for( j = 0; j < BINS; j++)
      {
         complex double *H1 = channels[ch_HFIELD1].X;
         complex double *H2 = channels[ch_HFIELD2].X;

         // N/S and E/W signals, correcting for loop azimuths
         complex double ew = (cos2 * H1[j] - cos1 * H2[j]) * det;
         complex double ns = (-sin2 * H1[j] + sin1 * H2[j]) * det;

         //  H-field signal in plane of incidence
         complex double or = ew * sin( ev->bearing) +
                             ns * cos( ev->bearing);

         XX[j] = or + channels[ch_EFIELD].X[j];
      }
   }
   else
   {
      for( j = 0; j < BINS; j++) XX[j] = channels[0].X[j];
   }
}

//
//  A pulse has been triggered and the time domain waveforms are in
//  channels[].buf with a small amount of pre-trigger.
//
//  Determine the TOGA of each channel, if possible.  Produce an amplitude
//  weighted average TOGA from the channels that gave a measurement.
//
//  Estimate the range by examining the dispersion.
//
//  If polar operation is called for, work out the bearing.
//

static void process_trigger( struct EVENT *ev)
{
VT_report( 3, "Trigger");

   ev->Tf = timestamp_add( Tin, (-buflen + 1) * DT);

   int ch, j;

   //
   //  Fourier transform each channel.
   //

   double power = 0;
   for( ch = 0; ch < chans; ch++)
   {
      struct CHAN *cp = channels + ch;

      //
      //  FFT the pulse and measure the RMS amplitude.  A duration of Tpulse
      //  seconds is analysed, the rest of the buffer duration Tfft is padded
      //  with zeros.
      //

      double sumsq = 0;
      int np = Tpulse * sample_rate;
      for( j = 0; j < FFTWID; j++)
      {
         double v = BUF(ch, j);
         if( j < np)
         {
            cp->fft[j] = v;
            sumsq += v * v;
         }
         else cp->fft[j] = 0;
      }
      cp->rms = sqrt(sumsq/np);
      power += cp->rms * cp->rms;

      fftw_execute( cp->fp);
   }

   ev->rms = sqrt( power);

   compute_bearing( ev);

   if( !compute_event( ev)) return;

   double sd2 = 0;
   int ns = 0;
   for( j = bf1; j <= bf2; j++)
   {
      if( ev->mask[j]) continue;

      double w = j * DF * 2 * M_PI;
      double wc = 1670 * 2 * M_PI;

      double x = 1/sqrt( 1 - wc*wc/w/w);
      double y = ev->ts_icept + ev->ts_slope * x;
      double d = ev->dphi[j] - y;

      sd2 += d*d;
      ns++;
   }

   double sd = sqrt( sd2/ns);

   for( j = bf1; j <= bf2; j++)
   {
      if( ev->mask[j]) continue;

      double w = j * DF * 2 * M_PI;
      double wc = 1670 * 2 * M_PI;

      double x = 1/sqrt( 1 - wc*wc/w/w);
      double y = ev->ts_icept + ev->ts_slope * x;
      double d = ev->dphi[j] - y;

      if( fabs( d) > 3 * sd) ev->mask[j] = TRUE;
   }

   compute_bearing( ev);

   if( !compute_event( ev)) return;

   if( ev->corr < limit_corr) return;
   if( ev->phresidual > limit_phres) return;
   if( ev->ascore > limit_ascore) return;

   output_record( ev);

   last_N++;
   N_out++;
   if( Nmax && N_out == Nmax) VT_exit( "completed %d", Nmax);

   thold = Thold * sample_rate;                    // Begin the hold-off period
}

//
//  The input buffer is a circular buffer of length buflen indexed through a
//  a macro BUF( channel, P).  P=0 is the oldest sample, P=buflen-1 is the
//  newest.  Tf is the timestamp of BUF(*,0) and Tin is the timestamp of the
//  latest sample BUF(*,buflen-1).
//
//                                                          Tin
//   |<-- Tpretrig -->|                                     |
//   XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
//   |                |
//   P=0              P=btrig
//          

//
//  Called after each input frame.  Test to see if anything triggers and if
//  so, call process_trigger().
//

static void evaluate_trigger( void)
{
   int ch;
   struct EVENT ev;

   if( CFLAG)   // Trigger on UT second marks
   {
      timestamp T = timestamp_add( Tin, (-buflen + 1 + btrig) * DT);
      
      double t = timestamp_frac( T) + Tpretrig;
      if( t < 1 && t + DT >= 1) 
      {
         init_event( &ev);
         process_trigger( &ev);
         free_event( &ev);
      }
      return;
   }

   if( one_shot)   // A trigger time has been given with -T
   {
      timestamp T = timestamp_add( Tin, (-buflen + 1 + btrig) * DT);
      if( timestamp_LT( T, Ttrig) &&
          timestamp_GE( timestamp_add( T, DT), Ttrig))
      {
         init_event( &ev);
         process_trigger( &ev);
         free_event( &ev);
         VT_exit( "completed trigger");
      }

      return;
   }

   //
   // Normal trigger test.  Hold-off period is restarted whenever the
   // signal rate of change is above the threshold.
   //

   if( thold) thold--;

   for( ch=0; ch<chans; ch++)
   {
      double d = BUF( ch, btrig+1) - BUF( ch, btrig);
      if( fabs(d) > trigger_level)
      {
         if( thold) thold = Thold * sample_rate;
         else
         {
            init_event( &ev);
            process_trigger( &ev);
            free_event( &ev);
         }
         break;
      }
   }
}

//
//  Revise the trigger threshold every AT_INT seconds.  The threshold is
//  changed by +/-10% according to whether the trigger rate over the last
//  AT_INT seconds is above or below the target rate.
//

static void evaluate_threshold( void)
{
   double rate = last_N / (double) AT_INT;

   if( rate < throttle) trigger_level *= 0.9;
   else trigger_level *= 1.1;

   VT_report( 1, "rate %.2f trigger %.3f", rate, trigger_level);
}

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

static void parse_foption( char *args)
{
   while( args && *args)
   {
      char *p = strchr( args, ',');
      if( p) p++;

      if( !strncmp( args, "corr=", 5)) limit_corr = atof( args+5);
      else
      if( !strncmp( args, "phres=", 6)) limit_phres = atof( args+6);
      else
      if( !strncmp( args, "ascore=", 7)) limit_ascore = atof( args+7);
      else
         VT_bailout( "unrecognised -f option: %s", args);

      args = p;
   }
}

int main( int argc, char *argv[])
{
   VT_init( "vttoga");

   int background = 0;
   char *polarspec = NULL;

   while( 1)
   {
      int c = getopt( argc, argv, "vBL:F:h:r:E:d:G:T:p:N:q:f:ec?");
      
      if( c == 'v') VT_up_loglevel();
      else
      if( c == 'B') background = 1;
      else
      if( c == 'E') Etime = atof( optarg);
      else
      if( c == 'L') VT_set_logfile( "%s", optarg);
      else
      if( c == 'F') VT_parse_freqspec( optarg, &F1, &F2);
      else
      if( c == 'd') outdir = strdup( optarg);
      else
      if( c == 'G') gran = atoi( optarg);
      else
      if( c == 'q') qfactor = atof( optarg);
      else
      if( c == 'p')
      {
         polarspec = strdup( optarg);
      }
      else
      if( c == 'T') Ttrig = VT_parse_timestamp( optarg);
      else
      if( c == 'r') 
      {
         throttle = atof( optarg);
         RFLAG = 1;
         if( throttle < 0) VT_bailout( "invalid -r option");
      }
      else
      if( c == 'e') EFLAG = 1;
      else
      if( c == 'c') CFLAG = 1;
      else
      if( c == 'N') Nmax = atoi( optarg);
      else
      if( c == 'h') trigger_level = atof( optarg);
      else
      if( c == 'f') parse_foption( strdup( optarg));
      else
      if( c == -1) break;
      else
         usage(); 
   }  
  
   if( argc > optind + 1) usage();
   char *bname = strdup( optind < argc ? argv[optind] : "-");
 
   if( background)
   {
      int flags = bname[0] == '-' ? KEEP_STDIN : 0;
      flags |= KEEP_STDOUT;
      VT_daemonise( flags);
   }

   struct VT_CHANSPEC *chspec = VT_parse_chanspec( bname);

   VTFILE *vtfile = VT_open_input( bname);
   if( !vtfile) VT_bailout( "cannot open: %s", VT_error);

   VT_init_chanspec( chspec, vtfile);
   chans = chspec->n;
   sample_rate = VT_get_sample_rate( vtfile);
   VT_report( 1, "channels: %d, sample_rate: %d", chans, sample_rate);

   if( !timestamp_is_ZERO( Ttrig)) one_shot = 1;

   if( polarspec)
   {
      VT_parse_polarspec( chans, polarspec,
                          &ch_HFIELD1, &polar1_align,
                          &ch_HFIELD2, &polar2_align,
                          &ch_EFIELD);

      if( ch_HFIELD1 >= 0 && ch_HFIELD2 >= 0) polar_mode = 1;
   }

   //
   //  Set up buffers lengths, etc.  If -T given, an input buffer is created
   //  to hold the given time window, otherwise a default circular buffer is
   //  created.
   // 

   buflen = Tbuf * sample_rate;
   btrig = Tpretrig * sample_rate;
   FFTWID = Tfft * sample_rate;
   BINS = FFTWID/2 + 1;
   DF = sample_rate/(double) FFTWID;
   DT = 1/(double)sample_rate;

   VT_report( 2, "buffer length: %d samples trig %d DF=%.3f",
                  buflen, btrig, DF);

   if( F2 <= F1) VT_bailout( "invalid frequency range");

   bf1 = F1/DF;
   bf2 = F2/DF;
   if( bf2 >= BINS) bf2 = BINS-1;

   channels = VT_malloc_zero( sizeof( struct CHAN) * chans);
   int i;
   for( i=0; i<chans; i++)
   {
      struct CHAN *cp = channels + i;

      cp->buf = VT_malloc( sizeof( double) * buflen);
      cp->fft = VT_malloc( sizeof( double) * FFTWID);
      cp->X = VT_malloc( sizeof( complex double) * BINS);
      cp->fp = fftw_plan_dft_r2c_1d( FFTWID, cp->fft, cp->X, FFTW_ESTIMATE);
   }

   XX = VT_malloc( sizeof( complex double) * BINS);

   if( !trigger_level) trigger_level = DEFAULT_THRESHOLD;

   double *frame;
   int ch;
   int nbuf = 0;

   Tstart = VT_get_timestamp( vtfile);
   last_T = timestamp_secs( Tstart);

   while( 1)
   {
      //
      // Read a frame and add to circular input buffers
      //
      Tin = VT_get_timestamp( vtfile); 

      if( (frame = VT_get_frame( vtfile)) == NULL) break;

      for( ch = 0; ch < chans; ch++)
      {
         double v = frame[chspec->map[ch]];
         channels[ch].buf[bp] = v;
      }

      bp = (bp + 1) % buflen;

      //
      // Once the buffer is full, start looking for triggers
      //

      if( nbuf < buflen) nbuf++;  
      else evaluate_trigger();

      //
      //  Reconsider the trigger threshold to aim for the target rate.
      //

      time_t t = timestamp_secs( Tin);
      if( RFLAG && t - last_T > AT_INT)
      {
         evaluate_threshold();
         last_T = t;
         last_N = 0;
      }

      //
      // Finish if reached a given end time.
      //

      if( Etime && timestamp_diff(Tin, Tstart) > Etime)
      {
         VT_report( 1, "completed %f seconds", Etime);
         break;
      }
   }

   return 0;
}

