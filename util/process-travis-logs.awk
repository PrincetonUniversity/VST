$1=="COMMIT" {
    now_in_commit($2);
    DATE[C]= $3 " " $4 " " $5 " " $2;
}
/^The Coq Proof Assistant, version/ {
    COQVERSION[C]=$6;
}
$1=="TIMINGS" {F=filenumber($10); T=$4+$6; M=$8/1000; TABLE[C,F,0]=T;}
/^XXXFinished transaction/ {
      T = $0; ++LINE; 
      sub(/Finished tra.* secs [(]/,"",T); sub(/u.*/,"",T);
      TABLE[C,F,LINE]=T;
      if (LINE>LINES[F]) LINES[F]=LINE;
      }
END{
    PROCINFO["sorted_in"] = "cmp_str_val"
/*    asort(DATE,INDEX,"cmp_str_val"); */
/*    for (I in INDEX) INVERT[INDEX[I]]=I; */
/*    for (I in DATE) printf "DATE %d %s\n", I, DATE[I]; */
/*    for (I in INVERT) printf "INVERT %s %d\n", I, INVERT[I]; */
/*    for (D in DATE) ORDER[countCOMMIT+1-INVERT[DATE[D]]]= D; */
/*    for (I in ORDER) printf "ORDER %d %d\n", I, ORDER[I]; */
/*    for(C in ORDER) printf "DATE[ORDER[]] %d %s\n", C, DATE[ORDER[C]]; */
    H++; printf("File\tLine\t");
    for (C=1;C<=countCOMMIT;C++)
         printf "%s\t", substr(COMMITS[C],1,7);
    printf "\n"; 
    H++; printf("DATE\t\t");
    for (C=1;C<=countCOMMIT;C++)
         printf "%s\t", substr(DATE[C],1,25);
    printf "\n";
    H++; printf("COQ\t\t");
    for (C=1;C<=countCOMMIT;C++)
        printf "%s\t", COQVERSION[C];
    printf "\n";
    H++; printf("TOTAL\t\t");
    T=countFILE;
    for (F in LINES) T += LINES[F];
    for (C=1;C<=countCOMMIT;C++)
	printf "=SUMIF($B%d:$B%d,0,%c%d:%c%d)\t",
	    1+H, T+H, C+66, 1+H, C+66, T+H;  /* 66 is ASCII 'B' */
    printf "\n";
    for (F in FILENAMES) {
	for (L=0; L<=LINES[F]; L++) {
	    H++;
	    printf "%s\t%d\t", FILENAMES[F],L;
	    COL=65;
            for (C=1;C<=countCOMMIT;C++) {
		T = TABLE[C,F,L];
		COL++;
		if (T==0)
		    printf "=%c%d\t", COL, H;
		else printf "%10.2f\t", T;
	    }
	    printf "\n"
	}
    }
}

function now_in_commit(COMMITNAME) {
    C = COMMITNUM[COMMITNAME];
    if (C==0) {
	C= ++countCOMMIT; 
	COMMITNUM[COMMITNAME]=C; 
	COMMITS[C]=COMMITNAME;
    }
}

function filenumber(NAME) {
    F = FILENUM[NAME];
    if (F==0) {
	F = ++countFILE; 
	FILENUM[NAME]=F;
	FILENAMES[F]=NAME;
    }
    return F;
}

function cmp_str_val(i1, v1, i2, v2)
{
    # string value comparison, ascending order
    v1 = v1 ""
    v2 = v2 ""
    if (v1 < v2) return -1
    if (v1 > v2) return 1;
    return 0;
}
