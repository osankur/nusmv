define(`ROOT_TIMEOUT',8)dnl
define(`NUMENTRIES_LIMIT', 3)dnl
define(`IGNORE_ROOT', 2)dnl
define(`MAXSEQ',7)dnl
define(`ROOTID',1)dnl
-- RESULTS FOR SYNCHRONOUS CASE
-- CASE IGNORE=3
-- For K=5, (5mins, 3mins) compte+=(28,32)
-- For K=4, (~10s)compte+=(9,17)
-- For K=3, (~1s) compte+=(8,12)
-- For K=2, (0s) compte=(7,9)
-- For K=1, (0s) compte=(8,8)
--
-- CAS IGNORE=2
-- For K=7, 13min, compte+=(30,42)
-- For K=6, 76s, compte+=(19,29)
-- For K=5, 16s, compte+=(13,17)
-- For K=4, 3s, compte+=(8,14)
-- For K=3, 1s, compte+=(7,11)
-- FOr K=2, 1s, compte+=(6,8)
define(`compteMAX',63)dnl
define(`for',`ifelse($#,0,``$0'',`ifelse(eval($2<=$3),1,`pushdef(`$1',$2)$4`'popdef(`$1')$0(`$1',incr($2),$3,`$4')')')')dnl
define(`STABLE_HB',eval(ROOT_TIMEOUT-1))
--
-- FTSP algorithm with a line topology represented concretely + the effect of other nodes represented very abstractly
--
-- Init: arbitrary offsets
-- 
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
	-- Is it time to decrement myseq variables (for normalization)?
	-- Here, the only tracked myseq are those that belong to procs with myroot=ROOT.
	-- Others have an arbitrary value, here 0.
	decrement_myseq := case
		-- Case where all relevant myseq >= 1
		state = norm & ( (p1.myroot = NONROOT | p1.myseq >= 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq >= 1)')) 
										 : TRUE;
		-- Case where all relevant myseq are 0 or >= 2
		state = norm & ( (p1.myroot = NONROOT | p1.myseq != 1) for(`j',2,N,` & (p`'j.myroot = NONROOT | p`'j.myseq != 1)')) 
										 : TRUE;
		TRUE: FALSE;
	esac;
	-- Is someone currently broadcasting? If broadcasting is true, then bc_source is the broadcasting node
	-- and (ROOT, bc_seqn) is the message.
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
-- INVARSPEC (p1.myroot = ROOT for(`j',2,N,`& p`'j.myroot = ROOT '))
-- LTLSPEC F(G(p`'N.myroot = ROOT))
-- INVARSPEC (p`'N.myroot = ROOT)
-- LTLSPEC F(G(p`'N.myroot = ROOT & p`'N.hb <= 4))
-- INVARSPEC (p`'N.myroot = ROOT )
--LTLSPEC F (G((compte >= 6 & (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot))));
--LTLSPEC F(compte = 12 & !(p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot));
--INVARSPEC (compte >= 6 -> (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & !p`'N.imroot));
--INVARSPEC (bounded_myseq & (compte >= 12 -> (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot)));
--
-- LTLSPEC F(G(p`'N.myroot = ROOT));
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB);
INVARSPEC (p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB & p`'N.numentries >= NUMENTRIES_LIMIT & !p`'N.imroot);
INVARSPEC (compte>=24 -> p`'N.myroot = ROOT & p`'N.hb <= STABLE_HB);



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
		-- Reset hb on discovering ROOT
		id != ROOTID & myroot = NONROOT & next(myroot) = ROOT : 0;
		-- 
		-- If OTHERS send us a newer message
		state = idle & id != ROOTID & myroot = ROOT & next(myseq) > myseq : 0;
		TRUE : hb;
	esac;
	next(myroot) := case
		-- Declaration of root by timeout
		state = update & hb >= ROOT_TIMEOUT & id != ROOTID : NONROOT;
		state = update & hb >= ROOT_TIMEOUT & id = ROOTID : ROOT;
		receiving  : ROOT;
		-- Simultaneous switch to ROOT during idle due to OTHERS
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
		-- Spontaneous increase in myseq due to OTHERS (up to main.root_seqn)
-- Switch to myseq of the previous node:
for(`i',2,N-1,dnl
	`main.state = select & id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
	')dnl
-- Switch to arbitrary values:
--for(`i',0,MAXSEQ,dnl
--`for(`j',i,MAXSEQ,dnl
--`		myroot = ROOT & id != ROOTID & state = idle & myseq = i & main.root_seqn = j : {i`'for(`k',eval(i+1),j,`,k')};
--')dnl
--')dnl
		myroot = NONROOT : 0;
		TRUE : myseq;
	esac;
INIT
	(myroot = ROOT -> myseq <= main.root_seqn)
	& (myroot = NONROOT -> myseq = 0);
DEFINE
	receiving := state = idle & main.broadcasting & main.bc_source = eval(N-1)
						& (imroot -> hb >= IGNORE_ROOT); -- The last process only receives from N-1
	broadcasting := (state = sending);

--- This are the first N-1 processes
--- They are assumed to have stabilized to myroot=ROOT already at the start
--  Removed variables myroot, imroot, and numentries which are constant
--
--  These processes are initialized with the following constraints:
--
--	P = hb <= 5 /\ numentries >= NUMENTRIES_LIMIT /\ (imroot <-> id=ROOTID) <-> myroot = ROOT /\ myseq = (id = ROOTID)? N-2 : {0,1,...,N-3}
-- 
--  
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
		id = ROOTID & state = sending & myseq < MAXSEQ : myseq + 1; -- Increase by ROOTID
		receiving & main.bc_seqn > myseq : main.bc_seqn;
		myroot = ROOT & main.decrement_myseq & (myseq >= 1) : myseq - 1; -- Normalization
		-- Spontaneous increase in myseq due to OTHERS (up to main.root_seqn)
--for(`i',0,MAXSEQ,dnl
--`for(`j',i,MAXSEQ,dnl
--`		myroot = ROOT & id != ROOTID & state = idle & myseq = i & main.root_seqn = j : {i`'for(`k',eval(i+1),j,`,k')};
--')dnl
--')dnl
for(`i',2,N-1,dnl
	`main.state = select & id = i & myroot = ROOT & state=idle & myseq < main.p`'eval(i-1).myseq : {myseq, main.p`'eval(i-1).myseq};
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

