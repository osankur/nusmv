-- ``Incremental'' model checking:
--================================
--			 The convergence with K=3 implies convergence of the first three nodes when K=4.
--       In fact, the effect of the 4th node is already captured by Others. 
-- 			 So to check K=4, we can start from a non-det state where the first three nodes have myroot=ROOT.
--			 There is a simulation relation that can be proven by hand though.
--
-- IDEA: Simplify the updates of myseq due to OTHERS 
--			 Only keep spontaneous updates to the value of the previous node
--			 This is justified in absence of link and node failures
--
-- TODO Use the shortest path abstraction: myseq can only spontaneously increase to that of the previous neighbor
-- This is justified in absence of link and node failures
-- Otherwise ROOT_TIMEOUT must increase with N, which is not OK. In other terms, the current abstraction is too coarse.
--
define(`ROOT_TIMEOUT',8)dnl
define(`NUMENTRIES_LIMIT', 3)dnl
define(`IGNORE_ROOT', 2)dnl
define(`MAXSEQ',7)dnl
define(`ROOTID',1)dnl
-- CAS IGNORE=3
-- For K=4, (30min,)compte+=(15,)
-- For K=3, (6s-17s) compte+=(9,13)
-- For K=2, (1s) compte=(7,10)

-- CAS IGNORE=2
-- For K=5, 65mins, compte+=(18,28)
-- For K=4, 130s, compte+=(10,16)
-- For K=3, 28s, compte+=(8,12)
-- FOr K=2, 1s, compte+=(6,9)
define(`compteMAX',63)dnl
define(`for',`ifelse($#,0,``$0'',`ifelse(eval($2<=$3),1,`pushdef(`$1',$2)$4`'popdef(`$1')$0(`$1',incr($2),$3,`$4')')')')dnl
define(`STABLE_HB',7)
-- Stable_HB: N=2 -> 3
-- Stable_HB: N=3 -> 5
-- Stable_HB: N=4 -> ??
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
	-- Is it time to decrement myseq variables (for normalization)?
	-- Here, the only tracked myseq are those that belong to procs with myroot=ROOT.
	-- Others have an arbitrary value, here 0.
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
	-- Is someone currently broadcasting? If broadcasting is true, then bc_target is the target node,
	-- and (ROOT, bc_seqn) is the message.
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
		receiving & imroot & hb < IGNORE_ROOT : myroot;
		receiving : ROOT;
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
	myroot = ROOT -> myseq <= main.root_seqn
	& (myroot = NONROOT -> myseq = 0);
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
		-- main.decrement_myseq & myroot = ROOT & bc_myseq = 0 : TRUE; -- Will be ignored anyway
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

