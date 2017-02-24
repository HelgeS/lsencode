/* Authors:
   Current version: Carla Gomes   <gomes@cs.cornell.edu>

   Previous versions
   Carla Gomes  <gomes@cs.cornell.edu>
   Henry Kautz   <kautz@cs.washington.edu>
   Yongshao Ruan <ruan@cs.washington.edu>
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef NT
#include <sys/times.h>
#include <sys/time.h>
#endif
#ifdef NT
#define random() rand()
#define srandom(seed) srand(seed)
#endif
#ifndef CLK_TCK
#define CLK_TCK 60
#endif

#define MAX_LINE_LENGTH 10000
#define MAX_NAME_LENGTH 10000

#define RANDOM 0
#define BALANCED 1

char linebuf[MAX_LINE_LENGTH+1];
char stringbuf[MAX_LINE_LENGTH+1];

/******************************************************************************/

int order = 0;			/* global variable for order of ls */
int **squarecolor;  /* squarecolor[i][j] == color assigned to that square if any
                                         == -1 if no color assigned */
int **squarefixed;  /* squarefixed[i][j] == 1 iff that square is colored,
                       		       == 0 iff color not yet determined */

/******************************************************************************/

int ***incidencecube;  /* incidencecube[i][j][k] ==
			      1 iff squarecolor[i][j] must be color k
			      0 iff squarecolor[i][j] *must not* be color k
			      -1 iff squarecolor[i][j] might or might not end up being k */
int ***mapvar;         /* mapvar[i][j][k] == the boolean variable that represents
			  the proposition that square[i,j] has color k
			  if that proposition has not been determined true or false yet.
                          If that proposition has been determined, then == -1. */
int nvar = -1;			/* number of boolean variables in the sat encoding */
int ncls = -1;			/* number of clauses in the sat encoding */
int *varval;			/* varval[i] holds value of variable i from .sol file */

/******************************************************************************/

/* ADD FORWARD DECLARATIONS OF ALL FUNCTIONS HERE! */
int satencode_pls(char*, int);
int nunfixed(void);
int init_incidencecube(void);
int forward_checking_incidencecube(void);
int poke(char*, int, unsigned long, char*, int);
int poke_rectangle(char*, int, char*);
int poke_banded(char*, int, char*);
int generate_random_holes(int);
int generate_rectangle_holes(int);
int generate_balanced_holes(int);
int generate_banded_holes(int );
int test_validity_squarecolor(void);
int read_ols_in_squarecolor(char*);
int read_pls_in_squarecolor(char*);
int read_varval(char*);
int write_pls(char*);
int alloc_varval(void);
int alloc_incidencecube(void);
int alloc_squarecolor(void);
int alloc_squarefixed(void);
void new_empty(char*);
void new_regular(char*);
void new_qcp(char*, int, unsigned long);
void new_balanced_qcp(char*, int, unsigned long);
int error(char*);
unsigned long getseed(void);
void shuffle(char*, char*, int, unsigned long);
int find_col(int, int, int);
int find_symb(int, int);
int find_row(int, int);
void permute(char*, char*, int, unsigned long);
void test_validity_squarecolor_2(void);

/******************************************************************************/


int main(int argc, char *argv[])
{
    int      i;
    char     command[MAX_NAME_LENGTH];
    char     infile[MAX_NAME_LENGTH];
    char     outfile[MAX_NAME_LENGTH];
    char     model[MAX_NAME_LENGTH];
    int      imodel;
    int      numhole;
    int      numrow;
    int      permutations, bandwidth;
    int      noise;
    unsigned long seed;
    int shuffles;
    FILE *fp;

    if (argc <= 1) {
        printf("Usage : %s new {empty | regular} OUTFILE ORDER\n", argv[0]);
        printf("Usage : %s new {qcp | bqcp} OUTFILE ORDER HOLES {SEED}\n", argv[0]);
        printf("Usage : %s shuffle INFILE SHUFFLES OUTFILE { SEED }\n", argv[0]);
        printf("Usage : %s poke {random | balanced | banded} INFILE NUMHOLE OUTFILE { SEED }\n", argv[0]);
        printf("Usage : %s poke randbal INFILE NUMHOLE NOISE(0-100) OUTFILE {SEED}\n", argv[0]);
        printf("Usage : %s poke rectangle INFILE NUMROW OUTFILE\n", argv[0]);
        printf("Usage : %s {permute} INFILE PERMUTATIONS OUTFILE { SEED }\n", argv[0]);
        printf("Usage : %s pls2sat INFILE { minimal }\n", argv[0]);
        printf("Usage : %s pls2color INFILE \n", argv[0]);
        printf("Usage : %s ols2pls INFILE\n", argv[0]);
        printf("Usage : %s forward INFILE { OUTFILE }\n", argv[0]);
        printf("Usage : %s sat2pls INFILE { OUTFILE }\n", argv[0]);
        exit(-1);
    }

    fp = fopen("record", "a");
    if (fp == NULL) error("Open file failure");
    fseek(fp, 0, 2);

    sscanf(argv[1], "%s", command);

    if (strcmp(command, "poke") == 0) {
        if (argc < 6) error("Bad arguments");
        sscanf(argv[2], "%s", model);
        sscanf(argv[3], "%s", infile);
        sscanf(argv[4], "%d", &numhole);
	if ((strcmp(model, "random") == 0) ||
	    (strcmp(model, "balanced") == 0)) {
	    sscanf(argv[5], "%s", outfile);
	    if (argc > 6)
	        sscanf(argv[6], "%lu", &seed);
	    else
	        seed = getseed();
	    if (strcmp(model, "random") == 0)
	      imodel = RANDOM;
	    else if (strcmp(model, "balanced") == 0)
	      imodel = BALANCED;

	    poke(infile, numhole, seed, outfile, imodel);
	    printf("%s poke: infile: %s  order: %d  holes: %d  outfile: %s  seed: %lu\n",
		   model, infile, order, numhole, outfile, seed);
	    fprintf(fp, "%s poke: infile: %s  order: %d  holes: %d  outfile: %s  seed: %lu\n",
		    model, infile, order, numhole, outfile, seed);
	}
	else if (strcmp(model, "randbal") == 0) {
            sscanf(argv[5], "%d", &noise);
	    sscanf(argv[6], "%s", outfile);
	    if (argc > 7)
	        sscanf(argv[7], "%lu", &seed);
	    else
	        seed = getseed();
	    poke_randbal(infile, numhole, noise, seed, outfile);
	    printf("randbal poke: infile: %s  order: %d  holes: %d  noise: %d  outfile: %s  seed: %lu\n",
		   infile, order, numhole, noise, outfile, seed);
	    fprintf(fp, "randbal poke: infile: %s  order: %d  holes: %d  noise: %d  outfile: %s  seed: %lu\n",
		    infile, order, numhole, noise, outfile, seed);
	}
	else if (strcmp(model, "rectangle") == 0) {
	    numrow = numhole;
	    sscanf(argv[5], "%s", outfile);
	    poke_rectangle(infile, numrow, outfile);
	    printf("rectangle poke: infile: %s  order: %d  rows: %d  numholes: %d  outfile: %s\n",
		   infile, order, numrow, numrow*order, outfile);
	    fprintf(fp, "rectangle poke: infile: %s  order: %d  rows: %d  numholes: %d  outfile: %s\n",
		    infile, order, numrow, numrow*order, outfile);
	}
	else if (strcmp(model, "banded") == 0) {
	    bandwidth = poke_banded(infile, numrow, outfile);
	    printf("banded poke: infile: %s  order: %d  numholes: %d  outfile: %s bandwidth: %d\n",
		   infile, order, numrow, outfile, bandwidth);
	    fprintf(fp, "banded poke: infile: %s  order: %d  numholes: %d  outfile: %s bandwidth: %d\n",
		    infile, order, numrow, outfile, bandwidth);
	}
	else {
	  error("Bad model");
	}
    } else if (strcmp(command, "permute") == 0) {
	if (argc < 5) error("Bad arguments");
	sscanf(argv[2], "%s", infile);
	sscanf(argv[3], "%d", &permutations);
	sscanf(argv[4], "%s", outfile);
	if (argc > 5)
	    sscanf(argv[5], "%lu", &seed);
	else
	    seed = getseed();
	permute(infile, outfile, permutations, seed);
        fprintf(fp, "permute: infile: %s  outfile: %s  permutations: %d  seed: %lu\n",
		infile, outfile, permutations, seed);
        printf("permute: infile: %s  outfile: %s  permutations: %d  seed: %lu\n",
		infile, outfile, permutations, seed);
   } else if (strcmp(command, "pls2color") == 0){
     if (argc < 3) error("Bad arguments");
     
     sscanf(argv[2], "%s", infile);
     read_pls_in_squarecolor(infile);

     alloc_incidencecube();
     init_incidencecube();
     
     colorencode_pls(infile);

   } else if (strcmp(command, "pls2sat") == 0){
        int orig_holes, final_holes;
	if (argc < 3) error("Bad arguments");
	
        sscanf(argv[2], "%s", infile);
        read_pls_in_squarecolor(infile);
        alloc_incidencecube();
        init_incidencecube();
        orig_holes = nunfixed();
        if (forward_checking_incidencecube()) error("incidence ??????");
        final_holes = nunfixed();
	alloc_mapvar();
	init_mapvar();
	
	printf("%s: infile: %s  order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
	       command, infile, order, orig_holes, final_holes, nvar);
	printf("%s: fwd_csp_bb: %d  fwd_csp_bb_frac: %f\n", 
	       command, orig_holes - final_holes, ((double)(orig_holes - final_holes))/orig_holes);
	printf("%s: fwd_bin_bb: %d  fwd_bin_bb_frac: %f\n",
	       command, orig_holes * order - nvar,
	       ((double)(orig_holes * order - nvar))/(orig_holes * order));

	satencode_pls(infile, (argc >= 4 && strcmp(argv[3],"minimal")==0));
	printf("%s: clauses: %d\n", command, ncls);
	fprintf(fp, "%s: infile: %s  order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
		command, infile, order, orig_holes, final_holes, nvar);

    } else if (strcmp(command, "forward") == 0) {
        int orig_holes, final_holes;
	if (argc < 3) error("Bad arguments");
	
        sscanf(argv[2], "%s", infile);
        read_pls_in_squarecolor(infile);
        alloc_incidencecube();
        init_incidencecube();
        orig_holes = nunfixed();
        if (forward_checking_incidencecube()) error("incidence ??????");
        final_holes = nunfixed();
	alloc_mapvar();
	init_mapvar();
	
	printf("%s: infile: %s  order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
	       command, infile, order, orig_holes, final_holes, nvar);
	printf("%s: fwd_csp_bb: %d  fwd_csp_bb_frac: %f\n", 
	       command, orig_holes - final_holes, ((double)(orig_holes - final_holes))/orig_holes);
	printf("%s: fwd_bin_bb: %d  fwd_bin_bb_frac: %f\n",
	       command, orig_holes * order - nvar,
	       ((double)(orig_holes * order - nvar))/(orig_holes * order));
	if (argc > 3){
	    sscanf(argv[3], "%s", outfile);
	    write_pls(outfile);
	    printf("%s: outfile: %s\n", command, outfile);
	}
	fprintf(fp, "%s: infile: %s  order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
		command, infile, order, orig_holes, final_holes, nvar);

    } else if (strcmp(command, "sat2pls") == 0) {
	if (argc < 3) error("Bad arguments");

        sscanf(argv[2], "%s", infile);
        read_pls_in_squarecolor(infile);
        alloc_incidencecube();
        init_incidencecube();
        if (forward_checking_incidencecube()) error("incidence ??????");
        alloc_mapvar();
        init_mapvar();
        fprintf(fp, "testsol: infile: %s  order: %d  binary_vars: %d\n", infile, order, nvar);
        read_varval(infile);
        test_validity_squarecolor();
        printf("testsol: The solution is valid\n");
	if (argc > 3) {
	    sscanf(argv[3], "%s", outfile);
	    write_pls(outfile);
	}

    } else if (strcmp(command, "new") == 0) {
	if (argc < 5) error("Bad arguments to new");
	sscanf(argv[3], "%s", outfile);
	sscanf(argv[4], "%d", &order);
	if (strcmp(argv[2],"empty")==0)
	    new_empty(outfile);
	else if (strcmp(argv[2],"regular")==0)
	    new_regular(outfile);
	else if (strcmp(argv[2],"qcp")==0){
	  if (argc < 6) error("Bad arguments");
	  sscanf(argv[5], "%d", &numhole);
	  if (argc > 6)
	    sscanf(argv[6], "%lu", &seed);
	  else
	    seed = getseed();
	    new_qcp(outfile, numhole, seed);
	}
	else if (strcmp(argv[2],"bqcp")==0){
	  if (argc < 6) error("Bad arguments");
	  sscanf(argv[5], "%d", &numhole);
	  if (argc > 6)
	    sscanf(argv[6], "%lu", &seed);
	  else
	    seed = getseed();
	    new_balanced_qcp(outfile, numhole, seed);
	}
	else error("Bad argument to new");
	if ((strcmp(argv[2],"qcp")==0) || (strcmp(argv[2],"bqcp")==0)){
	  fprintf(fp, "new: type: %s  lsname: %s  order: %d  numhole: %d  seed: %d\n", argv[2], outfile, order, numhole, seed);
	  printf("new: type: %s  lsname: %s  order: %d  numhole: %d  seed: %d\n", argv[2], outfile, order, numhole, seed);
	}
	else {
	  fprintf(fp, "new: type: %s  lsname: %s  order: %d\n", argv[2], outfile, order);
	  printf("new: type: %s  lsname: %s  order: %d\n", argv[2], outfile, order);
	}

    } else if (strcmp(command, "shuffle") == 0) {
	if (argc < 5) error("Bad arguments");
	sscanf(argv[2], "%s", infile);
	sscanf(argv[3], "%d", &shuffles);
	sscanf(argv[4], "%s", outfile);
	if (argc > 5)
	    sscanf(argv[5], "%lu", &seed);
	else
	    seed = getseed();
	shuffle(infile, outfile, shuffles, seed);
        fprintf(fp, "shuffle: infile: %s  outfile: %s  shuffles: %d  seed: %lu\n",
		infile, outfile, shuffles, seed);
        printf("shuffle: infile: %s  outfile: %s  shuffles: %d  seed: %lu\n",
		infile, outfile, shuffles, seed);

    } else if (strcmp(command, "ols2pls") == 0) {
	if (argc < 3) error("Bad arguments");
	sscanf(argv[2], "%s", infile);
        read_ols_in_squarecolor(infile);
	write_pls(infile);
        fprintf(fp, "ols2pls: infile: %s  order: %d\n", infile, order);
        printf("ols2pls: infile: %s  order: %d\n", infile, order);

    } else error("Unknown command");

    fclose(fp);

    exit(0);
}

/******************************************************************************/


int satencode_pls(char *outfile, int minflag)
{
    char  satfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j, k;
    int   i1, j1, k1;
    int   i2, j2, k2;
    int   flag = 0;
    int   nlit;
    int   lncls;		/* local version of ncls */

    strcpy(satfilename, outfile);
    strcat(satfilename, ".cnf");

    lncls = 0;

    /* We actually do this twice, since we don't know the number of
       clauses until we finish generating them the first time!
       ncls is set at the end of the first time through the loop. */

    loop :
    
	fp = fopen(satfilename, "w");
    fprintf(fp, "p cnf %d %d\n", nvar, ncls);

    if (!minflag){
	/* Binary mutex constraint: no two colors assigned to the same square */
	for (i = 0; i < order; i++) {
	    for (j = 0; j < order; j++) {
		for (k1 = 0; k1 < order -1 ; k1++) {
		    if (incidencecube[i][j][k1] == -1) {
			for (k2 = k1 + 1; k2 < order; k2++) {
			    if (incidencecube[i][j][k2] == -1) {
				fprintf(fp, "%8d", -(mapvar[i][j][k1] + 1));
				fprintf(fp, "%8d", -(mapvar[i][j][k2] + 1));
				fprintf(fp, "%8d\n", 0);
				lncls++;
			    }
			}
		    }
		}
	    }
	}
    }

    /* Binary mutex constraint: a color can appear at most once in each row */
    for (j = 0; j < order; j++) {
        for (k = 0; k < order; k++) {
            for (i1 = 0; i1 < order - 1 ; i1++) {
                if (incidencecube[i1][j][k] == -1) {
                    for (i2 = i1 + 1; i2 < order; i2++) {
                        if (incidencecube[i2][j][k] == -1) {
                            fprintf(fp, "%8d", -(mapvar[i1][j][k] + 1));
                            fprintf(fp, "%8d", -(mapvar[i2][j][k] + 1));
                            fprintf(fp, "%8d\n", 0);
                            lncls++;
                        }
                    }
                }
            }
        }
    }
    /* Binary mutex constraint: a color can appear at most once in each column */
    for (i = 0; i < order; i++) {
        for (k = 0; k < order; k++) {
            for (j1 = 0; j1 < order - 1 ; j1++) {
                if (incidencecube[i][j1][k] == -1) {
                    for (j2 = j1 + 1; j2 < order; j2++) {
                        if (incidencecube[i][j2][k] == -1) {
                            fprintf(fp, "%8d", -(mapvar[i][j1][k] + 1));
                            fprintf(fp, "%8d", -(mapvar[i][j2][k] + 1));
                            fprintf(fp, "%8d\n", 0);
                            lncls++;
                        }
                    }
                }
            }
        }
    }

    /* long positive clause: some color must be assigned to each uncolored square */
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            nlit = 0;
            for (k = 0; k < order ; k++) {
                if (incidencecube[i][j][k] == -1) {
                    fprintf(fp, "%8d", mapvar[i][j][k] + 1);
                    nlit++;
                }
            }
            if (nlit > 0) {
                fprintf(fp, "%8d\n", 0);
                lncls++;
            }
        }
    }

    if (!minflag){
	/* long positive clause: each color must appear at least once in each row */
	for (j = 0; j < order; j++) {
	    for (k = 0; k < order; k++) {
		nlit = 0;
		for (i = 0; i < order; i++) {
		    if (incidencecube[i][j][k] == -1) {
			fprintf(fp, "%8d", mapvar[i][j][k] + 1);
			nlit++;
		    }
		}
		if (nlit > 0) {
		    fprintf(fp, "%8d\n", 0);
		    lncls++;
		}
	    }
	}
	/* long positive clause: each color must appear at least once in each column */
	for (i = 0; i < order; i++) {
	    for (k = 0; k < order ; k++) {
		nlit = 0;
		for (j = 0; j < order; j++) {
		    if (incidencecube[i][j][k] == -1) {
			fprintf(fp, "%8d", mapvar[i][j][k] + 1);
			nlit++;
		    }
		}
		if (nlit > 0) {
		    fprintf(fp, "%8d\n", 0);
		    lncls++;
		}
	    }
	}
    }

    fclose(fp);

    if (flag == 0) {
	/* First time through the loop finished -- remember the number of clauses */
        flag = 1;
	ncls = lncls;
        goto loop;
    }

    return(0);
}



/******************************************************************************/



int colorencode_pls(char *outfile)
{
    char  colorfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j, k;
    int counter=0;


    strcpy(colorfilename, outfile);
    strcat(colorfilename, ".col");
    fp = fopen(colorfilename, "w");
    fprintf(fp, "c latin square or quasigroup  completion problem of order %2d with %4d holes\n",order,nunfixed() );
    fprintf(fp, "p %4d %6d\n", order*order, order*order*order-order*order);

    /* rows */
    for (i = 0; i < order; i++) {
      for (j = 0; j < order; j++) {
	for (k = j+1; k < order  ; k++) {
	  fprintf(fp, "e %4d %4d\n", i*order+j, i*order+k);
	  counter++;
	}
      }
    }



    printf("Total edges %d\n", counter);
    /* columns */
    for (j = 0; j < order; j++) {
      for (i = 0; i < order; i++) {
	for (k = i+1; k < order  ; k++) {
	  fprintf(fp, "e %4d %4d\n", i*order+j, k*order+k);
	  counter++;
	}
      }
    }

    for (i = 0; i < order; i++) {
      for (j = 0; j < order; j++) {
	if (squarefixed[i][j] == 1) {
	  fprintf(fp, "f %4d %4d\n", i*order+j, squarecolor[i][j]);
	}
      }
    }

    printf("Total edges %d\n", counter);
    fclose(fp);

    return(0);
}



/******************************************************************************/


int nunfixed(void)
{
    int i, j, k;
    int cnt;
    int nnunfixed = 0;

    /* Computes number of squares not yet assigned a definite color
       == number of holes */
    nvar = 0;
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            cnt = 0;
            for (k = 0; k < order; k++) {
                if (incidencecube[i][j][k] == -1) cnt++;
            }
            if (cnt != 0) nnunfixed++;
        }
    }
    return(nnunfixed);
}


/******************************************************************************/


int init_mapvar(void)
{
    int i, j, k;
    nvar = 0;
    /* Computes the number of binary variables and assigns the variables
       to positions in the incidencecube */

    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            for (k = 0; k < order; k++) {
                if (incidencecube[i][j][k] == -1) mapvar[i][j][k] = nvar++;
                else mapvar[i][j][k] = -1;
            }
        }
    }
    return(0);
}


/******************************************************************************/


int init_incidencecube(void)
{
    int i, j, k;
    int i1, j1, k1;

    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            for (k = 0; k < order; k++) {
                incidencecube[i][j][k] = -1;
            }
        }
    }

    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            if (squarefixed[i][j] == 1) {
                k = squarecolor[i][j];
                incidencecube[i][j][k] = 1;
                for (i1 = 0; i1 < order; i1++) if (i1 != i) {
                    if (incidencecube[i1][j][k] == 1) error("incidence ??????");
                    incidencecube[i1][j][k] = 0;
                }
                for (j1 = 0; j1 < order; j1++) if (j1 != j) {
                    if (incidencecube[i][j1][k] == 1) error("incidence ??????");
                    incidencecube[i][j1][k] = 0;
                }
                for (k1 = 0; k1 < order; k1++) if (k1 != k) {
                    if (incidencecube[i][j][k1] == 1) error("incidence ??????");
                    incidencecube[i][j][k1] = 0;
                }
            }
        }
   }
    return(0);
}

/******************************************************************************/



int forward_checking_incidencecube(void)
{
    int i, j, k;
    int i1, j1, k1;
    int holecnt, holei, holej, holek;
    int flag;

    loop :
    flag = 0;

    /* Look at each square to find ones that have only a single coloring option left */
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {

	    /* Count how many free options there are for coloring square[i,j] */
            holecnt = 0;
            for (k = 0; k < order; k++) {
                if (incidencecube[i][j][k] == -1) {
                    holecnt++;
                    holek = k;
                }
            }
	    /* If there is a just single option left, then in fact square[i,j] must 
	       in fact be that color */
            if (holecnt == 1) {
		/* set flag to remember that we made a change */
                flag = 1;
                k = holek;
                incidencecube[i][j][k] = 1;
                squarecolor[i][j] = k; squarefixed[i][j] = 1;
		/* Now that this square is colored, propagate this decision up and down */
                for (i1 = 0; i1 < order; i1++) if (i1 != i) {
                    if (incidencecube[i1][j][k] == 1) return 1;
                    incidencecube[i1][j][k] = 0;
                }
                for (j1 = 0; j1 < order; j1++) if (j1 != j) {
                    if (incidencecube[i][j1][k] == 1) return 1;
                    incidencecube[i][j1][k] = 0;
                }
		/* This is actually unnecessary since this was the last option,
		   but it cannot hurt */
                for (k1 = 0; k1 < order; k1++) if (k1 != k) {
                    if (incidencecube[i][j][k1] == 1) return 1;
                    incidencecube[i][j][k1] = 0;
                }
            }
        }
    }

    /* Repeat with the cube rotated 90 degrees.
       Now for each row and color, look for ones that have only a single column option left */
    for (j = 0; j < order; j++) {
        for (k = 0; k < order; k++) {
            holecnt = 0;
            for (i = 0; i < order; i++) {
                if (incidencecube[i][j][k] == -1) {
                    holecnt++;
                    holei = i;
                }
            }
            if (holecnt == 1) {
                flag = 1;
                i = holei;
                incidencecube[i][j][k] = 1;
                squarecolor[i][j] = k; squarefixed[i][j] = 1;
                for (i1 = 0; i1 < order; i1++) if (i1 != i) {
                    if (incidencecube[i1][j][k] == 1) return 1;
                    incidencecube[i1][j][k] = 0;
                }
                for (j1 = 0; j1 < order; j1++) if (j1 != j) {
                    if (incidencecube[i][j1][k] == 1) return 1;
                    incidencecube[i][j1][k] = 0;
                }
                for (k1 = 0; k1 < order; k1++) if (k1 != k) {
                    if (incidencecube[i][j][k1] == 1) return 1;
                    incidencecube[i][j][k1] = 0;
                }
            }
        }
    }
    /* Repeat with the cube rotated another 90 degrees.
       Now for each column and color, look for ones that have only a single row option left */
    for (i = 0; i < order; i++) {
        for (k = 0; k < order; k++) {
            holecnt = 0;
            for (j = 0; j < order; j++) {
                if (incidencecube[i][j][k] == -1) {
                    holecnt++;
                    holej = j;
                }
            }
            if (holecnt == 1) {
                flag = 1;
                j = holej;
                incidencecube[i][j][k] = 1;
                squarecolor[i][j] = k; squarefixed[i][j] = 1;
                for (i1 = 0; i1 < order; i1++) if (i1 != i) {
                    if (incidencecube[i1][j][k] == 1) return 1;
                    incidencecube[i1][j][k] = 0;
                }
                for (j1 = 0; j1 < order; j1++) if (j1 != j) {
                    if (incidencecube[i][j1][k] == 1) return 1;
                    incidencecube[i][j1][k] = 0;
                }
                for (k1 = 0; k1 < order; k1++) if (k1 != k) {
                    if (incidencecube[i][j][k1] == 1) return 1;
                    incidencecube[i][j][k1] = 0;
                }
            }
        }
    }

    /* If a change was made, start all over again.  This will still converge
       in polytime. */
    if (flag == 1) goto loop;

    return(0);
}

/******************************************************************************/

int poke(char *infile, int numhole, unsigned long seed, char *plsname, int model)
{
    srandom(seed);
    read_pls_in_squarecolor(infile);
    test_validity_squarecolor();

    switch (model) {
    case RANDOM:
        generate_random_holes(numhole);
	break;
    case BALANCED:
        generate_balanced_holes(numhole);
    }
    write_pls(plsname);
}


/******************************************************************************/

int poke_randbal(char *infile, int numhole, int noise, unsigned long seed, char *plsname)
{
    srandom(seed);
    read_pls_in_squarecolor(infile);
    test_validity_squarecolor();
    generate_randbal_holes(numhole, noise);
    write_pls(plsname);
}

/******************************************************************************/

int poke_rectangle(char *infile, int numrow, char *plsname)
{
    read_pls_in_squarecolor(infile);
    test_validity_squarecolor();
    generate_rectangle_holes(numrow);
    write_pls(plsname);
}


/******************************************************************************/

int poke_banded(char *infile, int numhole, char *plsname)
{
    int bandwidth;
    read_pls_in_squarecolor(infile);
    test_validity_squarecolor();
    bandwidth = generate_banded_holes(numhole);
    write_pls(plsname);
    return bandwidth;
}


/******************************************************************************/

int generate_random_holes(int numhole)
{
    int i, j;
    int *posvector, npos;
    int selectedpos;
    int wherepos;

    if (numhole > order * order) error("Number of holes exceed order square");

    posvector = (int *)malloc(sizeof(int) * order * order);
    for (i = 0; i < order * order; i++) posvector[i] = i;
    npos = order * order;

    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) squarefixed[i][j] = 1;
    }
    for (i = 0; i < numhole; i++) {
        wherepos = random() % npos;
        selectedpos = posvector[wherepos];
        if (squarefixed[selectedpos%order][selectedpos/order] != 1) error("??");
        squarefixed[selectedpos%order][selectedpos/order] = 0;
        posvector[wherepos] = posvector[--npos];
    }

    return(0);
}


/******************************************************************************/

int generate_rectangle_holes(int numrow)
{
    int i, j;

    if (numrow > order ) error("Number of rows exceed order");

    for (i = 0; i < numrow; i++) {
      for (j = 0; j < order; j++) {
        if (squarefixed[i][j] != 1) error("??");
        squarefixed[i][j] = 0;
      }
    }

    return(0);
}



/******************************************************************************/
/*
balanced QWH 
*/

int generate_balanced_holes(int numhole)
{
    int n, i, j, k, i1, j1;
    int num_color, min_num_color;
    int *posvector, npos;
    int *propagatedcolors;
    int selectedpos;
    int wherepos;

    if (numhole > order * order) error("Number of holes exceed order square");

    posvector = (int *)malloc(sizeof(int) * order * order);
    propagatedcolors = (int *)malloc(sizeof(int) * order * order);
    for (i = 0; i < order * order; i++) posvector[i] = 0;

    for (i = 0; i < order; i++) 
        for (j = 0; j < order; j++) {
	  squarefixed[i][j] = 1;
	  propagatedcolors[i*order+j] = 0;
	}

    alloc_incidencecube();
    init_incidencecube();
    for (n = 0; n < numhole; n++) {
        /* Find out the fewest/most number of propagated color of non-empty squares*/
        min_num_color = 2*order;
        for (i = 0; i < order; i++)
	  for (j = 0; j < order; j++) {
	    if (squarefixed[i][j] == 0) continue;
	    num_color = propagatedcolors[i*order+j];
	    if (min_num_color > num_color)
	      min_num_color = num_color;
	  }

        /* Find out the non-empty squares with the fewest/most number of propagated color*/
	npos = 0;
        for (i = 0; i < order; i++)
	  for (j = 0; j < order; j++) {
	    if (squarefixed[i][j] == 0) continue;
	    num_color = propagatedcolors[i*order+j];
	    if (num_color == min_num_color) {
	      posvector[npos++] = i * order + j;
	    }
	  }

        wherepos = random() % npos;
        selectedpos = posvector[wherepos];
	i = selectedpos / order;
	j = selectedpos % order;
	k = squarecolor[i][j];

        if (squarefixed[i][j] != 1) error("Balanced generate holes???");
        squarefixed[i][j] = 0;

	// propoage to the squares in the same column
	for (i1 = 0; i1 < order; i1++)
	  propagatedcolors[i1*order+j]++;
	// propoage to the squares in the same row
	for (j1 = 0; j1 < order; j1++)
	  propagatedcolors[i*order+j1]++;

    }

    return(0);
}


/******************************************************************************/
/*
random balanced QWH 
*/

int generate_randbal_holes(int numhole, int noise)
{
    int numhole_rand, numhole_bal;
    int i, j;
    int *posvector, npos;
    int selectedpos;
    int wherepos;

    if (numhole > order * order) error("Number of holes exceed order square");

    numhole_rand = (int) numhole * noise / 100;
    numhole_bal = numhole - numhole_rand;

    // first generate a part of holes in balanced model
    generate_balanced_holes(numhole_bal);
    
    // and then generate the rest holes in random model

    posvector = (int *)malloc(sizeof(int) * (order * order - numhole_bal));
    npos = 0;
    for (i = 0; i < order; i++)
        for (j = 0; j < order; j++)
	    if (squarefixed[i][j] == 1)
	        posvector[npos++] = i + j * order;

    for (i = 0; i < numhole_rand; i++) {
        wherepos = random() % npos;
        selectedpos = posvector[wherepos];
        if (squarefixed[selectedpos%order][selectedpos/order] != 1) error("??");
        squarefixed[selectedpos%order][selectedpos/order] = 0;
        posvector[wherepos] = posvector[--npos];
    }

    return(0);
}
   

/******************************************************************************/

int generate_banded_holes(int numhole)
{
    int i, j;
    int numempty = 0, bandwidth = 0;

    if ((numhole > (order*order)) || (numhole < 0) ) error("Number of holes");

    for (i = 0; i < order; i++) {
      for (j = 0; j < order - i; j++) {
	if (numempty == numhole) break;
	if (squarefixed[j][j+i] != 1) error("??");
	squarefixed[j][j+i] = 0;
	numempty++;
      }
      bandwidth++;
      // have poked enough holes
      if (numempty == numhole) break;

      // only need to do once for the diagonal
      if (i == 0) continue;

      for (j = 0; j < order - i; j++) {
	if (numempty == numhole) break;
	if (squarefixed[j+i][j] != 1) error("??");
	squarefixed[j+i][j] = 0;
	numempty++;
      }
      bandwidth++;
      // have poked enough holes
      if (numempty == numhole) break;
    }

    return(bandwidth);
}


/******************************************************************************/

/* Input infile.pls, permute it, and output outfile.pls */
void permute(char * infile, char * outfile, int total_permutation, unsigned long seed) {
  int *permutation;
  double *rnums;
  double tmp;
  int i, j, index, num_permutation;
  int **squarecolor_copy, **squarefixed_copy;

  // read square color from infile
  read_pls_in_squarecolor(infile);

  // set random seed
  srandom(seed);

  permutation = (int *)malloc(sizeof(int) * order);
  rnums = (double *)malloc(sizeof(double) * order);

  squarecolor_copy = (int **)malloc(sizeof(int *) * order);
  for (i = 0; i < order; i++) {
    squarecolor_copy[i] = (int *)malloc(sizeof(int) * order);
  }
  
  squarefixed_copy = (int **)malloc(sizeof(int *) * order);
  for (i = 0; i < order; i++) {
    squarefixed_copy[i] = (int *)malloc(sizeof(int) * order);
  }

  for (num_permutation = 0; num_permutation < total_permutation; num_permutation++) {

    // get an array of random double number between 0 and 1
    for (i = 0; i < order; i++)
      rnums[i] = (double) random()/RAND_MAX;


    // sort rnums
    for (i = 0; i < order; i++) {
      index = 0;
      for (j = 0; j < order; j++)
	if ((j != i) && (rnums[j] >= rnums[i])) {
	  if (rnums[j] != rnums[i])
	    index++;
	  else 
	    if (j < i) index++;
	}
      permutation[index] = i;
    }

    // keep a copy of squarefixed and squarecolor before row permutation
    for (i = 0; i < order; i++)
      for (j = 0; j < order; j++) {
	squarefixed_copy[i][j] = squarefixed[i][j];
	squarecolor_copy[i][j] = squarecolor[i][j];
      }

    // row permutation   
    for (i = 0; i < order; i++)
      for (j = 0; j < order; j++) {
	squarefixed[i][j] = squarefixed_copy[permutation[i]][j];
	squarecolor[i][j] = squarecolor_copy[permutation[i]][j];
      }

    // get an array of random double number between 0 and 1
    for (i = 0; i < order; i++)
      rnums[i] = (double) random()/RAND_MAX;

    // sort rnums
    for (i = 0; i < order; i++) {
      index = 0;
      for (j = 0; j < order; j++)
	if ((j != i) && (rnums[j] >= rnums[i])) {
	  if (rnums[j] != rnums[i])
	    index++;
	  else 
	    if (j < i) index++;
	}
      permutation[index] = i;
    }

    // keep a copy of squarefixed and squarecolor before column permutation
    for (i = 0; i < order; i++)
      for (j = 0; j < order; j++) {
	squarefixed_copy[i][j] = squarefixed[i][j];
	squarecolor_copy[i][j] = squarecolor[i][j];
      }

    // column permutation   
    for (j = 0; j < order; j++)
      for (i = 0; i < order; i++) {
	squarefixed[i][j] = squarefixed_copy[i][permutation[j]];
	squarecolor[i][j] = squarecolor_copy[i][permutation[j]];
      }
  }

  //write square color to outfile
  write_pls(outfile);
}
  

/******************************************************************************/

int test_validity_squarecolor(void)
{
    int i, j;
    int color;
    int *markvector;

    markvector = (int *)malloc(sizeof(int) * order);
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) markvector[j] = 0;
        for (j = 0; j < order; j++) {
            color = squarecolor[i][j];
            if ((color >= 0)&&(color <= order - 1)) markvector[color] = 1;
        }
        for (j = 0; j < order; j++) {
            if (markvector[j] == 0) error("The latin square is not valid...");
        }
        for (j = 0; j < order; j++) markvector[j] = 0;
        for (j = 0; j < order; j++) {
            color = squarecolor[j][i];
            if ((color >= 0)&&(color <= order - 1)) markvector[color] = 1;
        }
        for (j = 0; j < order; j++) {
            if (markvector[j] == 0) error("The latin square is not valid...");
        }
    }
    free(markvector);
}

/******************************************************************************/

int read_ols_in_squarecolor(char *olsname)
{
    char  olsfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j;
    int   n;

    strcpy(olsfilename, olsname);
    strcat(olsfilename, ".ols");

    fp = fopen(olsfilename, "r");
    if (fp == NULL) error("Read_ols_in_squarecolor failed to open file");
    
    fgets(linebuf, MAX_LINE_LENGTH, fp);
    sscanf(linebuf, "%s %d", stringbuf, &order); 
    while (strcmp(stringbuf, "Order:")!=0) {
        fgets(linebuf, MAX_LINE_LENGTH, fp);
        sscanf(linebuf, "%s %d", stringbuf, &order); 
    }
    fgets(linebuf, MAX_LINE_LENGTH, fp);
    sscanf(linebuf, "%s", stringbuf);
    while (strcmp(stringbuf, "New")!=0) {
        fgets(linebuf, MAX_LINE_LENGTH, fp);
        sscanf(linebuf, "%s", stringbuf);
    }

    alloc_squarecolor();
    alloc_squarefixed();

    fscanf(fp, "%s", stringbuf);
    for (i = 0; i < order; i++) {
        fscanf(fp, "%s", stringbuf);
        for (j = 0; j < order; j++) {
            fscanf(fp, "%d", &squarecolor[i][j]);
            fscanf(fp, "%s", stringbuf);
        }
    }
    //printf("File loaded\n");

    return(0);
}

/******************************************************************************/

int read_pls_in_squarecolor(char *infile)
{
    char  plsfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j;
    int   n;
    int numHoles=0;

    strcpy(plsfilename, infile);
    strcat(plsfilename, ".pls");

    fp = fopen(plsfilename, "r");
    if (fp == NULL) error("Read_pls_in_squarecolor failed to open file");
    
    fgets(linebuf, MAX_LINE_LENGTH, fp);
    sscanf(linebuf, "%s %d", stringbuf, &order); 
    while (strcmp(stringbuf, "order")!=0) {
        fgets(linebuf, MAX_LINE_LENGTH, fp);
        sscanf(linebuf, "%s %d", stringbuf, &order); 
    }

    alloc_squarecolor();
    alloc_squarefixed();

    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            fscanf(fp, "%d", &squarecolor[i][j]);
            if (squarecolor[i][j] != -1) squarefixed[i][j] = 1;
            else {
	      squarefixed[i][j] = 0;
	      numHoles++;
	    }   
        }
    }
    //printf("PLS File loaded\n");

    return(0);
}

/******************************************************************************/

int read_varval(char *infile)
{
    char  solfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j, k;
    int   n;
    int   cnt = 0;

    strcpy(solfilename, infile);
    strcat(solfilename, ".sol");

    fp = fopen(solfilename, "r");
    if (fp == NULL) error("Read_varval failed to open file");
   
    alloc_varval();

    // read variable value from the solution file
    for (i = 0; i < nvar; i++) {
        fscanf(fp, "%d", &n);
        if (n > 0) {
            varval[n-1] = 1;
        } else {
            varval[-n-1] = 0;
        }
    }

    for (n = 0; n < nvar; n++) if (varval[n] == 1) {
        cnt = 0;
        for (i = 0; i < order; i++) {
            for (j = 0; j < order; j++) {
                for (k = 0; k < order; k++) {
                    if (mapvar[i][j][k] == n) {
                        squarecolor[i][j] = k;
			squarefixed[i][j] = 1;
                        cnt++;
                    }
                }
            }
        }
    }

    for (i = 0; i < order; i++) {
      for (j = 0; j < order; j++) {
	printf("%3d", squarecolor[i][j]);
      }
      printf("\n");
    }
    return(0);
}


/******************************************************************************/

int write_pls(char *outfile)
{
    char  plsfilename[MAX_NAME_LENGTH];
    FILE  *fp;
    int   i, j;

    strcpy(plsfilename, outfile);
    strcat(plsfilename, ".pls");

    fp = fopen(plsfilename, "w");

    fprintf(fp, "order %d\n", order);
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            if (squarefixed[i][j] == 1) fprintf(fp, "%4d", squarecolor[i][j]);
            else fprintf(fp, "%4d", -1);
        }
        fprintf(fp, "\n");
    }

    return(0);
}

/******************************************************************************/

int alloc_varval(void)
{
    int i;
    varval = (int *)malloc(sizeof(int) * nvar);
    return(0);
}

int alloc_mapvar(void)
{
    int i, j;
    mapvar = (int ***)malloc(sizeof(int **) * order);
    for (i = 0; i < order; i++) {
        mapvar[i] = (int **)malloc(sizeof(int *) * order);
        for (j = 0; j < order; j++) {
            mapvar[i][j] = (int *)malloc(sizeof(int) * order);
        }
    }
    return(0);
}

int alloc_incidencecube(void)
{
    int i, j;
    incidencecube = (int ***)malloc(sizeof(int **) * order);
    for (i = 0; i < order; i++) {
        incidencecube[i] = (int **)malloc(sizeof(int *) * order);
        for (j = 0; j < order; j++) {
            incidencecube[i][j] = (int *)malloc(sizeof(int) * order);
        }
    }
    return(0);
}

int alloc_squarecolor(void)
{
    int i;
    squarecolor = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) {
        squarecolor[i] = (int *)malloc(sizeof(int) * order);
    }
    return(0);
}

int alloc_squarefixed(void)
{
    int i;
    squarefixed = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) {
        squarefixed[i] = (int *)malloc(sizeof(int) * order);
    }
    return(0);
}

/******************************************************************************/

/* Output a completely empty latin square */
void new_empty(char * plsname)
{
    int i, j;

    alloc_squarecolor();
    alloc_squarefixed();
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            squarecolor[i][j] = -1;
            squarefixed[i][j] = 0;
        }
    }
    alloc_incidencecube();
    init_incidencecube();
    write_pls(plsname);
}

/******************************************************************************/

/* Output the regular completely solved latin square */
void new_regular(char * outfile)
{
    int i, j;

    alloc_squarecolor();
    alloc_squarefixed();
    for (i = 0; i < order; i++) {
        for (j = 0; j < order; j++) {
            squarecolor[i][j] = (i+j) % order;
            squarefixed[i][j] = 1;
        }
    }
    alloc_incidencecube();
    init_incidencecube();
    write_pls(outfile);
}


/******************************************************************************/

/* Output the partial latin square with number of holes */
void new_qcp(char * outfile, int numhole, unsigned long seed)
{
    int i, j, k, l, num_uncolored_square;
    int ***colorvector, **available_color, *uncolored_square;
    int **saved_squarecolor, **saved_squarefixed;
    int selectedcolor, selectedsquare, wherepos;
    int failed = 1, attempts = 0;
    int orig_holes, final_holes;

    if (numhole > order * order) error("Number of holes exceed order square");

    srandom(seed);
    alloc_squarecolor();
    alloc_squarefixed();
    alloc_incidencecube();

    // allocate colorvetor
    colorvector = (int ***)malloc(sizeof(int **) * order);
    for (i = 0; i < order; i++) {
        colorvector[i] = (int **)malloc(sizeof(int *) * order);
        for (j = 0; j < order; j++) {
            colorvector[i][j] = (int *)malloc(sizeof(int) * order);
        }
    }
    // allocate available_color
    available_color = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        available_color[i] = (int *)malloc(sizeof(int) * order);
    // allocate uncolored_square
    uncolored_square = (int *)malloc(sizeof(int ) * order * order);
    // allocate saved_squarecolor
    saved_squarecolor = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        saved_squarecolor[i] = (int *)malloc(sizeof(int) * order);
    // allocate saved_squarefixed
    saved_squarefixed = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        saved_squarefixed[i] = (int *)malloc(sizeof(int) * order);

    while (failed && attempts++ < 1000) {
      failed = 0;
      // initialize
      for (i = 0, num_uncolored_square = 0; i < order; i++)
	for (j = 0; j < order; j++) {
	  squarecolor[i][j] = -1;
	  squarefixed[i][j] = 0;
	  available_color[i][j] = order; // Initially each square has all the color choices
	  uncolored_square[num_uncolored_square++] = i * order + j;
	  for (k = 0; k < order; k++)
	    colorvector[i][j][k] = k; // Keep all the color choices
	}

      while (num_uncolored_square > numhole) {
	// pick a random uncolored square
	wherepos = random() % num_uncolored_square;
	selectedsquare = uncolored_square[wherepos];
	i = selectedsquare / order;
	j = selectedsquare % order;
	uncolored_square[wherepos] = uncolored_square[--num_uncolored_square];

	// pick a random color for the square
	wherepos = random() % available_color[i][j];
	selectedcolor = colorvector[i][j][wherepos];
	squarecolor[i][j] = selectedcolor;
	squarefixed[i][j] = 1;

	// propagate the effect of this choice

	// On i-th row
	for (k = 0; k < order && !failed; k++) {
	  if (squarefixed[i][k]) continue; // omit the colored squared
	  for (l = 0; l < available_color[i][k]; l++)
	    if (colorvector[i][k][l] == selectedcolor) {
	      if (--available_color[i][k] == 0) {
		failed = 1;
		break;
	      }
	      colorvector[i][k][l] = colorvector[i][k][available_color[i][k]];
	      break;
	    }
	}
	if (failed) break;
	// On j-th colomn
	for (k = 0; k < order && !failed; k++) {
	  if (squarefixed[k][j]) continue;
	  for (l = 0; l < available_color[k][j]; l++)
	    if (colorvector[k][j][l] == selectedcolor) {
	      if (--available_color[k][j] == 0) {
		failed = 1;
		break;
	      }
	      colorvector[k][j][l] = colorvector[k][j][available_color[k][j]];
	      break;
	    }
	}
	if (failed) break;
      }

      if (failed) continue;

      init_incidencecube();

      // save the state of squarecolor and squarefixed
      for (k = 0; k < order; k++)
	for (l = 0; l < order; l++) {
	  saved_squarecolor[k][l] = squarecolor[k][l];
	  saved_squarefixed[k][l] = squarefixed[k][l];
	}

      orig_holes = numhole;
      // perform full forward checking
      if (forward_checking_incidencecube()) { // if detect inconsistency
	failed = 1;
	continue;
      }
      else {
        final_holes = nunfixed();
	alloc_mapvar();
	init_mapvar();
	printf("new qcp: outfile: %s order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
	       outfile, order, orig_holes, final_holes, nvar);
	printf("new qcp: fwd_csp_bb: %d  fwd_csp_bb_frac: %f\n", 
	       orig_holes - final_holes, ((double)(orig_holes - final_holes))/orig_holes);
	printf("new qcp: fwd_bin_bb: %d  fwd_bin_bb_frac: %f\n",
	       orig_holes * order - nvar,
	       ((double)(orig_holes * order - nvar))/(orig_holes * order));

      }	
      // restore the state of squarecolor and squarefixed
      for (k = 0; k < order; k++)
	for (l = 0; l < order; l++) {
	  squarecolor[k][l] = saved_squarecolor[k][l];
	  squarefixed[k][l] = saved_squarefixed[k][l];
	}
    }
    if (failed)
      error("Failed to generate a quasigroup completion problem\n");
    else
      write_pls(outfile);
}


/******************************************************************************/

/* Output a balanced partial latin square with given number of holes */
void new_balanced_qcp(char * outfile, int numhole, unsigned long seed)
{
    int i, j, k, l, num_uncolored_square;
    int ***colorvector, **available_color;
    int **saved_squarecolor, **saved_squarefixed;
    int selectedcolor, selectedsquare, wherepos;
    int failed = 1, attempts = 0;
    int orig_holes, final_holes;

    int num_color, min_num_color;
    int *squarevector, numsquare;
    int *propagatedcolors;

    if (numhole > order * order) error("Number of holes exceed order square");

    srandom(seed);
    alloc_squarecolor();
    alloc_squarefixed();
    alloc_incidencecube();

    squarevector = (int *)malloc(sizeof(int) * order * order);
    propagatedcolors = (int *)malloc(sizeof(int) * order * order);

    // allocate colorvetor
    colorvector = (int ***)malloc(sizeof(int **) * order);
    for (i = 0; i < order; i++) {
        colorvector[i] = (int **)malloc(sizeof(int *) * order);
        for (j = 0; j < order; j++) {
            colorvector[i][j] = (int *)malloc(sizeof(int) * order);
        }
    }
    // allocate available_color
    available_color = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        available_color[i] = (int *)malloc(sizeof(int) * order);
    // allocate saved_squarecolor
    saved_squarecolor = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        saved_squarecolor[i] = (int *)malloc(sizeof(int) * order);
    // allocate saved_squarefixed
    saved_squarefixed = (int **)malloc(sizeof(int *) * order);
    for (i = 0; i < order; i++) 
        saved_squarefixed[i] = (int *)malloc(sizeof(int) * order);


    while (failed && attempts++ < 1000) {
      // initialize
      failed = 0;
      num_uncolored_square = order * order;
      for (i = 0; i < order * order; i++) squarevector[i] = 0;
      for (i = 0; i < order; i++)
	for (j = 0; j < order; j++) {
	  squarecolor[i][j] = -1;
	  squarefixed[i][j] = 0;
	  propagatedcolors[i*order+j] = 0;
	  available_color[i][j] = order; // Initially each square has all the color choices
	  for (k = 0; k < order; k++)
	    colorvector[i][j][k] = k; // Keep all the color choices
	}

      while (num_uncolored_square > numhole) {

        /* Find out the fewest number of propagated color of empty squares*/
        min_num_color = order * order;
        for (i = 0; i < order; i++)
	  for (j = 0; j < order; j++) {
	    if (squarefixed[i][j] == 1) continue;
	    num_color = propagatedcolors[i*order+j];
	    if (min_num_color > num_color)
	      min_num_color = num_color;
	  }

        /* Find out the empty squares with the fewest number of propagated color*/
	numsquare = 0;
        for (i = 0; i < order; i++)
	  for (j = 0; j < order; j++) {
	    if (squarefixed[i][j] == 1) continue;
	    num_color = propagatedcolors[i*order+j];
	    if (num_color == min_num_color) {
	      squarevector[numsquare++] = i * order + j;
	    }
	  }

	// pick a random uncolored square
        wherepos = random() % numsquare;
        selectedsquare = squarevector[wherepos];
	i = selectedsquare / order;
	j = selectedsquare % order;

	// pick a random color for the square
	wherepos = random() % available_color[i][j];
	selectedcolor = colorvector[i][j][wherepos];
	squarecolor[i][j] = selectedcolor;
	squarefixed[i][j] = 1;
        num_uncolored_square--;

	//propogate the effect of the square and color choice

	// On i-th row
	for (k = 0; k < order; k++)
	  propagatedcolors[k*order+j]++;
	for (k = 0; k < order && !failed; k++) {
	  if (squarefixed[i][k]) continue; // omit the colored squared
	  for (l = 0; l < available_color[i][k]; l++)
	    if (colorvector[i][k][l] == selectedcolor) {
	      if (--available_color[i][k] == 0) {
		failed = 1;
		break;
	      }
	      colorvector[i][k][l] = colorvector[i][k][available_color[i][k]];
	      break;
	    }
	}
	if (failed) break;

	// On j-th colomn
	for (k = 0; k < order; k++)
	  propagatedcolors[i*order+k]++;
	for (k = 0; k < order && !failed; k++) {
	  if (squarefixed[k][j]) continue;
	  for (l = 0; l < available_color[k][j]; l++)
	    if (colorvector[k][j][l] == selectedcolor) {
	      if (--available_color[k][j] == 0) {
		failed = 1;
		break;
	      }
	      colorvector[k][j][l] = colorvector[k][j][available_color[k][j]];
	      break;
	    }
	}
	if (failed) break;
      }

      if (failed) continue;

      init_incidencecube();

      // save the state of squarecolor and squarefixed
      for (k = 0; k < order; k++)
	for (l = 0; l < order; l++) {
	  saved_squarecolor[k][l] = squarecolor[k][l];
	  saved_squarefixed[k][l] = squarefixed[k][l];
	}

      orig_holes = numhole;
      // perform full forward checking
      if (forward_checking_incidencecube()) { // if detect inconsistency
	failed = 1;
	continue;
      }
      else {
        final_holes = nunfixed();
	alloc_mapvar();
	init_mapvar();
	printf("new qcp: outfile: %s order: %d  holes: %d  csp_vars: %d  binary_vars: %d\n",
	       outfile, order, orig_holes, final_holes, nvar);
	printf("new qcp: fwd_csp_bb: %d  fwd_csp_bb_frac: %f\n", 
	       orig_holes - final_holes, ((double)(orig_holes - final_holes))/orig_holes);
	printf("new qcp: fwd_bin_bb: %d  fwd_bin_bb_frac: %f\n",
	       orig_holes * order - nvar,
	       ((double)(orig_holes * order - nvar))/(orig_holes * order));
      }	
      // restore the state of squarecolor and squarefixed
      for (k = 0; k < order; k++)
	for (l = 0; l < order; l++) {
	  squarecolor[k][l] = saved_squarecolor[k][l];
	  squarefixed[k][l] = saved_squarefixed[k][l];
	}
    }
    if (failed)
      error("Failed to generate a quasigroup completion problem\n");
    else
      write_pls(outfile);
}


/******************************************************************************/

int error(char *message)
{
    printf("%s\n", message);
    exit(1);
}

/******************************************************************************/

unsigned long getseed(void)
{
    struct timeval tv;
    struct timezone tzp;
    gettimeofday(&tv,&tzp);
    return (( tv.tv_sec & 0177 ) * 1000000) + tv.tv_usec;
}

/******************************************************************************/
// test validity of incidence cube
void test_validity_incidencecube(void){
  int i, j, k;
  int num_1=0;
  int num_neg1 =0;

  for (k=0;k<order;k++){
    for (i=0;i<order; i++){
      for (j=0;j<order;j++){
	if (incidencecube[i][j][k]==1) num_1++;
	if (incidencecube[i][j][k]==-1) num_neg1++;
	if ( incidencecube[i][j][k] < -1 || incidencecube[i][j][k] >1)
	  error("Check incidence cube error!");
      }
      if (((num_neg1 != 1) || (num_1 != 2)) && ((num_neg1 != 0) || (num_1 != 1)))
	error("Check incidence cube error!");

      num_1 =0;
      num_neg1 =0;
    }
    for (j=0;j<order; j++){
      for (i=0;i<order;i++){
	if (incidencecube[i][j][k]==1) {num_1++;}
	if (incidencecube[i][j][k]==-1) {num_neg1++;}
	if ( incidencecube[i][j][k] < -1 || incidencecube[i][j][k] >1)
	  error("Check incidence cube error!");
      }
      if (((num_neg1 != 1) || (num_1 != 2)) && ((num_neg1 != 0) || (num_1 != 1)))
	error("Check incidence cube error!");

      num_1 =0;
      num_neg1 =0;
    }
  }
}

/******************************************************************************/
// set colors to latin square according to incidence cube
void ic_ls_proper(void) {
  int i, j, k;

  for (i=0; i<order; i++)
    for (j=0; j<order; j++)
      for (k=0; k<order; k++)
      if  (incidencecube[i][j][k]== 1)
	squarecolor[i][j] = k;
}

/******************************************************************************/
// set incidence cube according to the color setting of latin square
void ls_ic_proper(void){
  int i, j , k;

  for (i=0; i<order; i++)
    for (j=0; j<order; j++)
      for (k=0; k<order; k++)
	if  (squarecolor[i][j]== k)
	  incidencecube[i][j][k] = 1;
	else
	  incidencecube[i][j][k] = 0;
}

/******************************************************************************/
// check latin square colors
void test_validity_squarecolor_2(void){
  int i, j, k;

  for(i=0; i<order; i++)
    for(j=0; j<order; j++)
      for(k=j+1; k<order; k++)
	if (squarecolor[i][j] == squarecolor[i][k])
	  error("Check proper latin square failed!");
  for(i=0; i<order; i++)
    for(j=0; j<order; j++)
      for(k=i+1; k<order; k++)
	if (squarecolor[i][j] == squarecolor[k][j])
	  error("Check proper latin square failed!");
}

/******************************************************************************/

void print_incidencecube(void) {
  int i, j, k;
  for (i=0; i<order; i++)
    for (j=0; j<order; j++){
      for (k=0; k<order; k++)
	printf("%d ", incidencecube[i][j][k]);
      printf("\n");
    }
}

/******************************************************************************/

/* Input infile.pls, shuffle it, and output outfile.pls */
void shuffle(char * infile, char * outfile, int shuffles, unsigned long seed) {
  int CounterProper = 0;
  //int X_improper_cell, Y_improper_cell, Z_improper_cell;
  int col, col_prime, symb, s,symb_prime, r, r_prime, l,row;
  int i;
  int k, z, y;
 	
//  printf"test");
  //initialize thge seed 
  
  
  // read square color from infile and test its validity
  read_pls_in_squarecolor(infile);
  test_validity_squarecolor_2();

  // initialize incidence cube according to square color
  alloc_incidencecube();
  ls_ic_proper();
  
  //
  
  srand(seed);
  while ( CounterProper < shuffles) 
  {
 
   	//initialize proper arguments
   	
  	r_prime = rand() % order;
  	 
  	r = rand() % order;
  	
  	while (r_prime == r){ r = rand() % order;}
  	
  	l = rand() % order;
  	while (l <= 1) {l = rand() % order;}
  
 	s = rand() % order;
 	
 	 
 	
 	col_prime = -1;
 	symb_prime = -1;
 	col = -1;
 	row = -1;
 	 		
	//first subsequence of the second method dealing with row r_prime and r
	for(i = 1; i <= l; i++) 
	{
 	  
 	  	if (i == 1)
	  	{
 	 		col = Find_col(r_prime, s, -1);
	  		symb = Find_symb(r, col);
	  		if (symb == -1) error("error dealing with improper symbols");
	  		incidencecube[r_prime][col][symb]++;
	  		incidencecube[r_prime][col][s]--;
	  		incidencecube[r][col][symb]--;
	  		incidencecube[r][col][s]++;
	  	}
	  	else if (i == l)
	  	{
	  		col_prime = Find_col(r_prime, symb, col);
	  		if (col_prime != -1)
 	 		{
	  			row = Find_row(s, col_prime);
	  			if (row == -1) error("error dealing with improper rows");
	  			incidencecube[r_prime][col_prime][s]++;
	  			incidencecube[r_prime][col_prime][symb]--;
 	 			incidencecube[row][col_prime][s]--;
 	 			incidencecube[row][col_prime][symb]++;
 	 			col = col_prime;
 	 			r_prime = row;
 	 		}
	  	}
	  	else
	  	{
 	 		col_prime = Find_col(r_prime, symb, col);
 	 		if (col_prime != -1)
 	 		{
 	 			
  				symb_prime= Find_symb(r, col_prime);
  				if (symb_prime == -1) error("error dealing with improper symbols");
  				incidencecube[r_prime][col_prime][symb_prime]++;
 	 			incidencecube[r_prime][col_prime][symb]--;
  				incidencecube[r][col_prime][symb_prime]--;
  				incidencecube[r][col_prime][symb]++;
  			}
 	 		else 
 	 		{
 	 			
 	 			i = l + 1;  //a proper square was found in 
 	 		}
 	 		symb = symb_prime;
  			col = col_prime;
 	 		
 	 	}
 	 }
	
	
		//swap between r and a third row 
 	 if (r_prime == row)
	  {
	  	
	  	col_prime = Find_col(row, symb, col);
	  	while (col_prime != -1)
	  	{
 	 		symb_prime = Find_symb(r, col_prime);
	  		incidencecube[row][col_prime][symb_prime]++;
  			incidencecube[row][col_prime][symb]--;
 	 		incidencecube[r][col_prime][symb_prime]--;
  			incidencecube[r][col_prime][symb]++;
  			symb = symb_prime;
  			col = col_prime;
  			col_prime = Find_col(row, symb, col);
  		}
  	  }
  	   // set square color according to incidence cube
      ic_ls_proper();

      // test the validity of square color
      test_validity_squarecolor_2();
  	  //count
  	  CounterProper++;
  	
  }		
 
  

  //write square color to outfile
  write_pls(outfile);
}


/**************************************************************************************************/


int Find_col(int row, int symbol,int column)
{
	int new_col = 0;
	 
	//find the porper column
	while (new_col < order)
	{
		
		if (new_col != column && incidencecube[row][new_col][symbol] == 1)
		{
			return new_col;	
		}
		new_col++;
	}
	return -1;

}


/***************************************************************************************************/

int Find_symb(int row, int column)
{
	int new_symb = 0;
	
	//find proper symbol
	while (new_symb < order)
	{
		if (incidencecube[row][column][new_symb] == 1)
		{
			return new_symb;
		}
		new_symb++;
	}
	return -1;
}


/*******************************************************************************************************/

int Find_row(int  symbol, int column)
{
	int new_row = 0;
	 
	
	//find porper row
	while (new_row < order)
	{
		if (incidencecube[new_row][column][symbol] == 1)
		{
			return new_row;
		}
		new_row++;
	}
	return -1;
}
