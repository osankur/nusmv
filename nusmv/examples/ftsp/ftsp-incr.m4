-- Root Election of FTSP (Sensys04)
--
-- Abstract model with asynchronous communication for incremental verification.
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
define(`IGNORE_ROOT', 2)dnl
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
	next(offset[i]) := case
		state = offincr & (round = i) & p`'i.finishedSending & (offset[i]<DELTA) :  offset[i] + 1;
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
`		& (state = wait & round = i -> (offset[i] < DELTA | !p`'i.finishedSending))
')
	
DEFINE
	root_seqn := p1.myseq;
	root_myroot := ROOT;
	decrement_myseq := case
		-- Case where all relevant myseq >= 1
		state = norm & ( (p1.myroot = NONROOT | p1.myseq >= 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq >= 1)')) 
								 for(`j',1,N,`& (p`'j.finishedSending | p`'j.bc_myseq >= 1) ')
										 : TRUE;
		-- Case where all relevant myseq are 0 or >= 2
		state = norm & ( (p1.myroot = NONROOT | p1.myseq != 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq != 1)')) 
								 for(`j',1,N,`& (p`'j.finishedSending | p`'j.bc_myseq != 1) ')
										 : TRUE;
		TRUE: FALSE;
	esac;
	broadcasting := next(p1.broadcasting) for(`i',2,N,`| next(p`'i.broadcasting)');
	bc_seqn := case
for(`i',1,N,dnl
`		state = select & next(round) = i & next(p`'i.broadcasting) : p`'i.bc_myseq;
')
		TRUE : 0;
	esac;
	bc_target := case
for(`i',1,N,dnl
`		state = select & next(round) = i & next(p`'i.state) = broadcasting_left : i-1;
		state = select & next(round) = i & next(p`'i.state) = broadcasting_right : i+1;
')
		TRUE : 1;
	esac;
	bounded_myseq := TRUE for(`i',1,N,`& p`'i.myseq < MAXSEQ & p`'i.bc_myseq < MAXSEQ');
	stabilized := (p1.myroot = ROOT for(`j',2,N,`& p`'j.myroot = ROOT '));
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB);
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot);



-- This is the N-th process. There is no broadcasting right since it is the last one
MODULE last_proc(id, main)
VAR
	state : {idle, update, sending, broadcasting_left };
	hb : 0..ROOT_TIMEOUT;
	myroot : {ROOT, NONROOT};
	numentries : 0..NUMENTRIES_LIMIT;
	myseq : 0..MAXSEQ;
	bc_myseq : 0..MAXSEQ; -- broadcast data
	bc_leftdone : boolean; -- have we finished sending left?
	imroot : boolean;
ASSIGN
	--init(state) := idle;
	--init(hb) := 0;
	--init(myroot) := NONROOT;
	--init(numentries) := 0;
	init(myseq) := {0for(`i',1,N-1,`, i')};
	init(bc_myseq) := {0for(`i',1,N-1,`, i')};
	--init(bc_leftdone) := TRUE;
	--init(imroot) := FALSE;
	--
	next(state) := case
		state=idle & (main.state) = select & next(main.round) = id & finishedSending : update;
		state=idle & (main.state) = select & next(main.round) = id & !bc_leftdone : broadcasting_left;
		state=update & myroot = ROOT & (id = ROOTID | numentries >= NUMENTRIES_LIMIT) : sending;
		state=update : idle;
		state=sending : idle;
		state=broadcasting_left : idle;
		state=broadcasting_right : idle;
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
		receiving : ROOT;
		state = idle & id != ROOTID & myroot = NONROOT : {myroot, main.root_myroot};
		TRUE : myroot;
	esac;
	next(imroot) := case
		state = update & hb >= ROOT_TIMEOUT : TRUE;
		id = ROOTID & next(myroot) = NONROOT : FALSE;
		id != ROOTID & next(myroot) = ROOT : FALSE;
		TRUE : imroot;
	esac;
	-- numentries is only relevant when myroot = ROOT, and abstracted away otherwise
	next(numentries) := case
		id != ROOTID & next(myroot) = ROOT & (myroot = NONROOT | next(myseq) > myseq) & numentries < NUMENTRIES_LIMIT : numentries + 1;
		myroot = ROOT : numentries;
		TRUE : 0;
	esac;
	-- myseq is only relevant when myroot = ROOT, and abstracted away otherwise
	next(myseq) := case
		myroot = ROOT & id = ROOTID & state = sending & myseq < MAXSEQ : myseq + 1; -- Increase by ROOTID
		receiving & main.bc_seqn > myseq : main.bc_seqn;
		myroot = ROOT & main.decrement_myseq & (myseq >= 1) : myseq - 1; -- Normalization
-- Switch to myseq of the previous node:
for(`i',2,N-1,dnl
	`id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
	')dnl
		myroot = NONROOT : 0;
		TRUE : myseq;
	esac;
	next(bc_myseq) := case
		state = sending : myseq;
		myroot = ROOT & main.decrement_myseq & (bc_myseq >= 1) : bc_myseq - 1; -- Normalization
		finishedSending : 0;
		TRUE : bc_myseq;
  esac;
	next(bc_leftdone) := case
		id = 1 : TRUE;
		id > 1 & state = sending : FALSE;
		state = broadcasting_left : TRUE;
		TRUE : bc_leftdone;
	esac;
INIT
	myroot = ROOT -> myseq <= main.root_seqn;
DEFINE
	receiving := state = idle & main.broadcasting & main.bc_target = id;
	finishedSending := bc_leftdone;
	broadcasting := (state = broadcasting_left);

--- This are the first N-1 processes
--- They are assumed to have stabilized to myroot=ROOT already at the start
--  Removed variables myroot, imroot, and numentries which are constant
--
--  These processes are initialized with the following constraints:
--
--	P = hb <= 2K-1 /\ numentries >= NUMENTRIES_LIMIT /\ (imroot <-> id=ROOTID) <-> myroot = ROOT /\ myseq = (id = ROOTID)? N-2 : {0,1,...,N-3}
-- 
--  
MODULE stable_proc(id, main)
VAR
	state : {idle, update, sending, broadcasting_left, broadcasting_right};
	myseq : 0..MAXSEQ;
	bc_myseq : 0..MAXSEQ; -- broadcast data
	bc_leftdone : boolean; -- have we finished sending left
	bc_rightdone : boolean; -- have we finished sending right
ASSIGN
	init(state) := idle;
	init(myseq) := case
		id = ROOTID : eval(N-2);
		id != ROOTID : {0for(`i',1,N-3,`, i')};
	esac;
	init(bc_myseq) := 0;
	init(bc_leftdone) := TRUE;
	init(bc_rightdone) := TRUE;
	--
	next(state) := case
		state=idle & (main.state) = select & next(main.round) = id & finishedSending : update;
		state=idle & (main.state) = select & next(main.round) = id & bc_rightdone & !bc_leftdone : broadcasting_left;
		state=idle & (main.state) = select & next(main.round) = id & bc_leftdone & !bc_rightdone : broadcasting_right;
		state=idle & (main.state) = select & next(main.round) = id & (!bc_leftdone & !bc_rightdone) : {broadcasting_right, broadcasting_left};
		state=update : sending;
		state=update : idle;
		state=sending : idle;
		state=broadcasting_left : idle;
		state=broadcasting_right : idle;
		TRUE : state;
	esac;
	next(myseq) := case
		id = ROOTID & state = sending & myseq < MAXSEQ : myseq + 1; -- Increase by ROOTID
		receiving & main.bc_seqn > myseq : main.bc_seqn;
		myroot = ROOT & main.decrement_myseq & (myseq >= 1) : myseq - 1; -- Normalization
		-- Spontaneous increase in myseq due to OTHERS (up to main.root_seqn)
for(`i',2,N-1,dnl
	`id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
	')dnl
		myroot = NONROOT : 0;
		TRUE : myseq;
	esac;
	next(bc_myseq) := case
		state = sending : myseq;
		main.decrement_myseq & (bc_myseq >= 1) : bc_myseq - 1; -- Normalization
		finishedSending : 0;
		TRUE : bc_myseq;
  esac;
	next(bc_leftdone) := case
		id = 1 : TRUE;
		id > 1 & state = sending : FALSE;
		state = broadcasting_left : TRUE;
		TRUE : bc_leftdone;
	esac;
	next(bc_rightdone) := case
	  id = N : TRUE;
		id < N & state = sending : FALSE;
		state = broadcasting_right : TRUE;
		TRUE : bc_rightdone;
	esac;
DEFINE
	imroot := id = ROOTID;
	receiving := state = idle & main.broadcasting & main.bc_target = id;
	finishedSending := bc_leftdone & bc_rightdone;
	broadcasting := (state = broadcasting_left) | (state = broadcasting_right);
	myroot := ROOT;

