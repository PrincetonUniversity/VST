$1=="COMMIT" {
    now_in_commit($2);
    DATE[C]= $3 " " $4 " " $5;
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
    PROCINFO["sorted_in"] = "@ind_num_asc";
    asort(DATE,INDEX);
    for (I in INDEX) INVERT[INDEX[I]]=I;
/*    for (I in DATE) printf "DATE %d %s\n", I, DATE[I]; */
/*    for (I in INVERT) printf "INVERT %s %d\n", I, INVERT[I]; */
    for (D in DATE) ORDER[countCOMMIT+1-INVERT[DATE[D]]]= D;
/*    for (I in ORDER) printf "ORDER %d %d\n", I, ORDER[I]; */
/*    for(C in ORDER) printf "DATE[ORDER[]] %d %s\n", C, DATE[ORDER[C]]; */
    H++; printf("File\tLine\t");
    for(C in ORDER) printf "%s\t", COMMITS[ORDER[C]];
    printf "\n"; 
    H++; printf("\t\t");
    for(C in ORDER) printf "%s\t", DATE[ORDER[C]];
    printf "\n";
    H++; printf("\t\t");
    for(C in ORDER) printf "%s\t", COQVERSION[ORDER[C]];
    printf "\n";
    H++; printf("TOTAL\t\t");
    T=countFILE;
    for (F in LINES) T += LINES[F];
    for(C in ORDER)
	printf "=SUMIF($B%d:$B%d,0,%c%d:%c%d)\t",
	    1+H, T+H, C+66, C+66, 1+H, T+H;  /* 66 is ASCII 'B' */
    printf "\n";
    for(F=1; F<=countFILE; F++) {
	for (L=0; L<=LINES[F]; L++) {
	    printf "%s\t%d\t", FILENAMES[F],L;
	    for(C in ORDER) printf "%10.2f\t", TABLE[ORDER[C],F,L];
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
