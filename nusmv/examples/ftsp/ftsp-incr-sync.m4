-- Root Election of FTSP (Sensys04)
--
-- Abstract model with synchronous communication for incremental verification.
-- 
-- The model contains N nodes on a line starting at the future root.
-- The effect of other nodes are included via non-determinism.
-- See FM'16 submission for the details.
--
-- The specified INVARSPEC are meant to be satisfied *eventually*.
-- Either use the check_eventually_invar command or replace them with an LTLSPEC FG.
--
-- Author: Ocan Sankur
--
define(`ROOT_TIMEOUT',8)dnl
define(`NUMENTRIES_LIMIT', 3)dnl
define(`IGNORE_ROOT', 3)dnl
define(`MAXSEQ',7)dnl
define(`ROOTID',1)dnl
define(`compteMAX',63)dnl
define(`for',`ifelse($#,0,``$0'',`ifelse(eval($2<=$3),1,`pushdef(`$1',$2)$4`'popdef(`$1')$0(`$1',incr($2),$3,`$4')')')')dnl
define(`STABLE_HB',7)
MODULE main
VAR
	state : {select, wait, norm, offincr};
	round : 1..N;
for(`i',1,N-1,dnl
`	p`'i : stable_proc(i, self);
')
	p`'N : last_proc(N, self);
	offset : array 1..N of 0..DELTA;
	compte : 0..compteMAX;
ASSIGN
	init(state) := select;
	next(state) := case
		state = select : wait;
for(`i',1,N,dnl
`		state = wait & (round = i & next(p`'i.state) = idle) : offincr;
')dnl
		state = offincr : norm;
		state = norm : select;
		TRUE : state;
	esac;
for(`i',1,N,dnl
` 
	-- init(offset[i]) := 0;
	next(offset[i]) := case
		state = offincr & (round = i) & (offset[i]<DELTA) :  offset[i] + 1;
		state = norm & (offset[1] >= 1 for(`j',2,N,` & offset[j] >= 1')) : offset[i] - 1;
		TRUE : offset[i];
	esac; 
')dnl
	next(round) := case
		state != select : round;
		TRUE : {1for(`i',2,N,`,i')};
	esac;
	init(compte) := 0;
	next(compte) := case
		compte < compteMAX & state = norm & (offset[1] >= 1 for(`j',2,N,` & offset[j] >= 1')) : compte + 1;
		TRUE : compte;
  esac;
INVAR
	-- Approximate synchrony:
	TRUE 
for(`i',1,N,dnl
`		& (state = wait & round = i -> (offset[i] < DELTA ))
')
	
DEFINE
	root_seqn := p1.myseq;
	root_myroot := ROOT;
	decrement_myseq := case
		-- Case where all relevant myseq >= 1
		state = norm & ( (p1.myroot = NONROOT | p1.myseq >= 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq >= 1)')) 
										 : TRUE;
		-- Case where all relevant myseq are 0 or >= 2
		state = norm & ( (p1.myroot = NONROOT | p1.myseq != 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq != 1)')) 
										 : TRUE;
		TRUE: FALSE;
	esac;
	broadcasting := (p1.broadcasting) for(`i',2,N,`| (p`'i.broadcasting)');
	bc_seqn := case
for(`i',1,N,dnl
`		state = wait & (round) = i & (p`'i.broadcasting) : p`'i.myseq;
')
		TRUE : 0;
	esac;
	bc_source := case
for(`i',1,N,dnl
`		state = wait & (round) = i & (p`'i.state) = sending : i;
')
		TRUE : 1;
	esac;
	bounded_myseq := TRUE for(`i',1,N,`& p`'i.myseq < MAXSEQ');
	stabilized := (p1.myroot = ROOT for(`j',2,N,`& p`'j.myroot = ROOT '));
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB);
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot);



-- This is the N-th process. There is no broadcasting right since it is the last one
MODULE last_proc(id, main)
VAR
	state : {idle, update, sending};
	hb : 0..ROOT_TIMEOUT;
	myroot : {ROOT, NONROOT};
	numentries : 0..NUMENTRIES_LIMIT;
	myseq : 0..MAXSEQ;
	imroot : boolean;
ASSIGN
	--init(state) := idle;
	--init(hb) := 0;
	--init(myroot) := NONROOT;
	--init(numentries) := 0;
	init(myseq) := {0for(`i',1,N-1,`, i')};
	--init(bc_myseq) := {0for(`i',1,N-1,`, i')};
	--init(bc_leftdone) := TRUE;
	--init(imroot) := FALSE;
	--
	next(state) := case
		state=idle & (main.state) = select & next(main.round) = id : update;
		state=update & myroot = ROOT & (id = ROOTID | numentries >= NUMENTRIES_LIMIT) : sending;
		state=update : idle;
		state=sending : idle;
		TRUE : state;
	esac;
	next(hb) := case
		state = update & !imroot & hb >= ROOT_TIMEOUT : {0,hb}; -- Becoming root by timeout
		state = update & hb < ROOT_TIMEOUT : hb + 1; -- Regular tick
		id != ROOTID & receiving & next(myroot) = ROOT & main.bc_seqn > myseq : 0;
		id != ROOTID & myroot = NONROOT & next(myroot) = ROOT : 0;
		state = idle & id != ROOTID & myroot = ROOT & next(myseq) > myseq : 0;
		TRUE : hb;
	esac;
	next(myroot) := case
		state = update & hb >= ROOT_TIMEOUT & id != ROOTID : NONROOT;
		state = update & hb >= ROOT_TIMEOUT & id = ROOTID : ROOT;
		receiving & imroot & hb < IGNORE_ROOT : myroot;
		receiving  : ROOT;
		state = idle & id != ROOTID & myroot = NONROOT : {myroot, main.root_myroot};
		TRUE : myroot;
	esac;
	next(imroot) := case
		state = update & hb >= ROOT_TIMEOUT : TRUE;
		id = ROOTID & next(myroot) = NONROOT : FALSE;
		id != ROOTID & next(myroot) = ROOT : FALSE;
		TRUE : imroot;
	esac;
	next(numentries) := case
		id != ROOTID & next(myroot) = ROOT & (myroot = NONROOT | next(myseq) > myseq) & numentries < NUMENTRIES_LIMIT : numentries + 1;
		myroot = ROOT : numentries;
		TRUE : 0;
	esac;
	next(myseq) := case
		myroot = ROOT & id = ROOTID & state = sending & myseq < MAXSEQ : myseq + 1; -- Increase by ROOTID
		receiving & main.bc_seqn > myseq : main.bc_seqn;
		myroot = ROOT & main.decrement_myseq & (myseq >= 1) : myseq - 1; -- Normalization
for(`i',2,N-1,dnl
	`id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
	')dnl
		myroot = NONROOT : 0;
		TRUE : myseq;
	esac;
INIT
	myroot = ROOT -> myseq <= main.root_seqn;
DEFINE
	receiving := state = idle & main.broadcasting & main.bc_source = eval(N-1); -- The last process only receives from N-1
	broadcasting := (state = sending);

MODULE stable_proc(id, main)
VAR
	state : {idle, update, sending};
	myseq : 0..MAXSEQ;
ASSIGN
	init(state) := idle;
	init(myseq) := case
		id = ROOTID : eval(N-2);
		id != ROOTID : {0for(`i',1,N-3,`, i')};
	esac;
	next(state) := case
		state=idle & (main.state) = select & next(main.round) = id : update;
		state=update : sending;
		state=sending : idle;
		TRUE : state;
	esac;
	next(myseq) := case
		id = ROOTID & state = sending & myseq < MAXSEQ : myseq + 1;
		receiving & main.bc_seqn > myseq : main.bc_seqn;
		myroot = ROOT & main.decrement_myseq & (myseq >= 1) : myseq - 1;
for(`i',2,N-1,dnl
	`id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
	')dnl
		myroot = NONROOT : 0;
		TRUE : myseq;
	esac;
DEFINE
	imroot := id = ROOTID;
	receiving := state = idle & main.broadcasting & 
		(id > 1 & main.bc_source = id - 1 | id < N & main.bc_source = id + 1);
	broadcasting := (state = sending);
	myroot := ROOT;

