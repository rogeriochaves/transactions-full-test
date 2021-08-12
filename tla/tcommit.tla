------------------------------ MODULE TCommit ------------------------------

(***************************************************************************)
(* This specification is explained in "Transaction Commit", Lecture 5 of   *)
(* the TLA+ Video Course.                                                  *)
(***************************************************************************)
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[rm] is the state of resource manager rm.
-----------------------------------------------------------------------------
TCTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
        
TCInit ==   rmState = [r \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A r \in RM : rmState[r] # "committed" 
  (*************************************************************************)
  (* True iff no resource manager has decided to commit.                   *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r)  == \/ /\ rmState[r] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![r] = "committed"]
              \/ /\ rmState[r] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following part of the spec is not discussed in Video Lecture 5.  It *)
(* will be explained in Video Lecture 8.                                   *)
(***************************************************************************)
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol written as a temporal      *)
  (* formula.                                                              *)
  (*************************************************************************)

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
  (*************************************************************************)
  (* This theorem asserts the truth of the temporal formula whose meaning  *)
  (* is that the state predicate TCTypeOK /\ TCInvariant is an invariant   *)
  (* of the specification TCSpec.  Invariance of this conjunction is       *)
  (* equivalent to invariance of both of the formulas TCTypeOK and         *)
  (* TCConsistent.                                                         *)
  (*************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sun Aug 08 12:58:12 CEST 2021 by rchaves
\* Created Sat Aug 07 06:03:55 CEST 2021 by rchaves

------------------------------ MODULE TwoPhase ------------------------------

(***************************************************************************)
(* This specification is discussed in "Two-Phase Commit", Lecture 6 of the *)
(* TLA+ Video Course.  It describes the Two-Phase Commit protocol, in      *)
(* which a transaction manager (TM) coordinates the resource managers      *)
(* (RMs) to implement the Transaction Commit specification of module       *)
(* TCommit.  In this specification, RMs spontaneously issue Prepared       *)
(* messages.  We ignore the Prepare messages that the TM can send to the   *)
(* RMs.                                                                    *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an RM when it  *)
(* decides to abort.  Such a message would cause the TM to abort the       *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.                                                               *)
(***************************************************************************)
CONSTANT RM  \* The set of resource managers

VARIABLES
  rmState,       \* rmState[r] is the state of resource manager r.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared"
                 \* messages.
  msgs         
    (***********************************************************************)
    (* In the protocol, processes communicate with one another by sending  *)
    (* messages.  For simplicity, we represent message passing with the    *)
    (* variable msgs whose value is the set of all messages that have been *)
    (* sent.  A message is sent by adding it to the set msgs.  An action   *)
    (* that, in an implementation, would be enabled by the receipt of a    *)
    (* certain message is here enabled by the presence of that message in  *)
    (* msgs.  For simplicity, messages are never removed from msgs.  This  *)
    (* allows a single message to be received by multiple receivers.       *)
    (* Receipt of the same message twice is therefore allowed; but in this *)
    (* particular protocol, that's not a problem.                          *)
    (***********************************************************************)

Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the RM indicated by the message's rm field to the TM.       *)
  (* Messages of type "Commit" and "Abort" are broadcast by the TM, to be  *)
  (* received by all RMs.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"Prepared", "Abort"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]
   
TPTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "done"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Messages

TPInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(r) ==
  (*************************************************************************)
  (* The TM receives a "Prepared" message from resource manager r.  We     *)
  (* could add the additional enabling condition r \notin tmPrepared,      *)
  (* which disables the action if the TM has already received this         *)
  (* message.  But there is no need, because in that case the action has   *)
  (* no effect; it leaves the state unchanged.                             *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> r] \in msgs
  /\ tmPrepared' = tmPrepared \cup {r}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a "Prepared" message.                     *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMRcvAbort(r) ==
  (*************************************************************************)
  (* The TM receives a "Abort" message from resource manager r. *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "done"
  /\ [type |-> "Abort", rm |-> r] \in msgs
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

\*TMAbort ==
\*  (*************************************************************************)
\*  (* The TM spontaneously aborts the transaction.                          *)
\*  (*************************************************************************)
\*  /\ tmState = "init"
\*  /\ tmState' = "done"
\*  /\ msgs' = msgs \cup {[type |-> "Abort"]}
\*  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(r) == 
  (*************************************************************************)
  (* Resource manager r prepares.                                          *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMChooseToAbort(r) ==
  (*************************************************************************)
  (* Resource manager r spontaneously decides to abort.  As noted above, r *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ msgs' = msgs \union {[type |-> "Abort", rm |-> r]}
  /\ UNCHANGED <<tmState, tmPrepared>>

RMRcvCommitMsg(r) ==
  (*************************************************************************)
  (* Resource manager r is told by the TM to commit.                       *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(r) ==
  (*************************************************************************)
  (* Resource manager r is told by the TM to abort.                        *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit
  \/ \E r \in RM : 
       TMRcvPrepared(r) \/ TMRcvAbort(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
         \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
-----------------------------------------------------------------------------
(***************************************************************************)
(* The material below this point is not discussed in Video Lecture 6.  It  *)
(* will be explained in Video Lecture 8.                                   *)
(***************************************************************************)

TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>
  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

THEOREM TPSpec => []TPTypeOK
  (*************************************************************************)
  (* This theorem asserts that the type-correctness predicate TPTypeOK is  *)
  (* an invariant of the specification.                                    *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Two-Phase Commit protocol implements the         *)
(* Transaction Commit protocol of module TCommit.  The following statement *)
(* imports all the definitions from module TCommit into the current        *)
(* module.                                                                 *)
(***************************************************************************)
INSTANCE TCommit 

THEOREM TPSpec => TCSpec
  (*************************************************************************)
  (* This theorem asserts that the specification TPSpec of the Two-Phase   *)
  (* Commit protocol implements the specification TCSpec of the            *)
  (* Transaction Commit protocol.                                          *)
  (*************************************************************************)
(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states, in a little over a    *)
(* minute on a 1 GHz PC.                                                   *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Sat Aug 07 12:21:33 CEST 2021 by rchaves
\* Created Sat Aug 07 06:47:33 CEST 2021 by rchaves


----------------------------- MODULE PaxosCommit ----------------------------
(***************************************************************************)
(* This specification is discussed in "Paxos Commit", Lecture 6 of the     *)
(* TLA+ Video Course.                                                      *)
(*                                                                         *)
(* This module specifies the Paxos Commit algorithm.  We specify only      *)
(* safety properties, not liveness properties.  We simplify the            *)
(* specification in the following ways.                                    *)
(*                                                                         *)
(*  - As in the specification of module TwoPhase, and for the same         *)
(*    reasons, we let the variable msgs be the set of all messages that    *)
(*    have ever been sent.  If a message is sent to a set of recipients,   *)
(*    only one copy of the message appears in msgs.                        *)
(*                                                                         *)
(*  - We do not explicitly model the receipt of messages.  If an           *)
(*    operation can be performed when a process has received a certain set *)
(*    of messages, then the operation is represented by an action that is  *)
(*    enabled when those messages are in the set msgs of sent messages.    *)
(*    (We are specifying only safety properties, which assert what events  *)
(*    can occur, and the operation can occur if the messages that enable   *)
(*    it have been sent.)                                                  *)
(*                                                                         *)
(*  -  We do not model leader selection.  We define actions that the       *)
(*    current leader may perform, but do not specify who performs them.    *)
(*                                                                         *)
(* As in the specification of Two-Phase commit in module TwoPhase, we have *)
(* RMs spontaneously issue Prepared messages and we ignore Prepare         *)
(* messages.                                                               *)
(***************************************************************************)
EXTENDS Integers

Maximum(S) == 
  (*************************************************************************)
  (* If S is a set of numbers, then this define Maximum(S) to be the       *)
  (* maximum of those numbers, or -1 if S is empty.                        *)
  (*************************************************************************)
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n >= m

CONSTANT RM,             \* The set of resource managers.
         Acceptor,       \* The set of acceptors.
         Majority,       \* The set of majorities of acceptors
         Ballot          \* The set of ballot numbers

(***************************************************************************)
(* We assume the following properties of the declared constants.           *)
(***************************************************************************)
ASSUME  
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
\*  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}
       (********************************************************************)
       (* All we assume about the set Majority of majorities is that any   *)
       (* two majorities have non-empty intersection.                      *)
       (********************************************************************)
       
Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  There are messages of type         *)
  (* "Commit" and "Abort" to announce the decision, as well as messages    *)
  (* for each phase of each instance of ins of the Paxos consensus         *)
  (* algorithm.  The acc field indicates the sender of a message from an   *)
  (* acceptor to the leader; messages from a leader are broadcast to all   *)
  (* acceptors.                                                            *)
  (*************************************************************************)
  [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}] 
      \cup
  [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
   val : {"prepared", "aborted", "none"}, acc : Acceptor] 
      \cup
  [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
      \cup                              
  [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,  
   val : {"prepared", "aborted"}] 
      \cup
  [type : {"Commit", "Abort"}]
-----------------------------------------------------------------------------
VARIABLES
  rmState,  \* rmState[r] is the state of resource manager r.
  aState,   \* aState[ins][ac] is the state of acceptor ac for instance 
            \* ins of the Paxos algorithm. 
  msgs      \* The set of all messages ever sent.

PCTypeOK ==  
  (*************************************************************************)
  (* The type-correctness invariant.  Each acceptor maintains the values   *)
  (* mbal, bal, and val for each instance of the Paxos consensus           *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Messages

PCInit ==  \* The initial predicate.
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |-> 
                 [ac \in Acceptor 
                    |-> [mbal |-> 0, bal  |-> -1, val  |-> "none"]]]
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(*                                THE ACTIONS                              *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup {m}
  (*************************************************************************)
  (* An action expression that describes the sending of message m.         *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(*                               RM ACTIONS                                *)
(***************************************************************************)
RMPrepare(r) == 
  (*************************************************************************)
  (* Resource manager r prepares by sending a phase 2a message for ballot  *)
  (* number 0 with value "prepared".                                       *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState
  
RMChooseToAbort(r) ==
  (*************************************************************************)
  (* Resource manager r spontaneously decides to abort.  It may (but need  *)
  (* not) send a phase 2a message for ballot number 0 with value           *)
  (* "aborted".                                                            *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(r) ==
  (*************************************************************************)
  (* Resource manager r is told by the leader to commit.  When this action *)
  (* is enabled, rmState[r] must equal either "prepared" or "committed".   *)
  (* In the latter case, the action leaves the state unchanged (it is a    *)
  (* ``stuttering step'').                                                 *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(r) ==
  (*************************************************************************)
  (* Resource manager r is told by the leader to abort.  It could be in    *)
  (* any state except "committed".                                         *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                            LEADER ACTIONS                               *)
(*                                                                         *)
(* The following actions are performed by any process that believes itself *)
(* to be the current leader.  Since leader selection is not assumed to be  *)
(* reliable, multiple processes could simultaneously consider themselves   *)
(* to be the leader.                                                       *)
(***************************************************************************)
Phase1a(bal, r) ==
  (*************************************************************************)
  (* If the leader times out without learning that a decision has been     *)
  (* reached on resource manager r's prepare/abort decision, it can        *)
  (* perform this action to initiate a new ballot bal.  (Sending duplicate *)
  (* phase 1a messages is harmless.)                                       *)
  (*************************************************************************)
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, r) ==
  (*************************************************************************)
  (* The action in which a leader sends a phase 2a message with ballot     *)
  (* bal > 0 in instance r, if it has received phase 1b messages for       *)
  (* ballot number bal from a majority of acceptors.  If the leader        *)
  (* received a phase 1b message from some acceptor that had sent a phase  *)
  (* 2b message for this instance, then maxbal \geq 0 and the value val    *)
  (* the leader sends is determined by the phase 1b messages.  (If         *)
  (* val = "prepared", then r must have prepared.) Otherwise, maxbal = -1  *)
  (* and the leader sends the value "aborted".                             *)
  (*                                                                       *)
  (* The first conjunct asserts that the action is disabled if any commit  *)
  (* leader has already sent a phase 2a message with ballot number bal.    *)
  (* In practice, this is implemented by having ballot numbers partitioned *)
  (* among potential leaders, and having a leader record in stable storage *)
  (* the largest ballot number for which it sent a phase 2a message.       *)
  (*************************************************************************)
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = r
  /\ \E MS \in Majority :    
        LET mset == {m \in msgs : /\ m.type = "phase1b"
                                  /\ m.ins  = r
                                  /\ m.mbal = bal 
                                  /\ m.acc  \in MS}
            maxbal == Maximum({ m.bal :  m \in mset })
            val == IF maxbal = -1 
                     THEN "aborted"
                     ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

PCDecide == 
  (*************************************************************************)
  (* A leader can decide that Paxos Commit has reached a result and send a *)
  (* message announcing the result if it has received the necessary phase  *)
  (* 2b messages.                                                          *)
  (*************************************************************************)
  /\ LET Decided(r, v) ==
           (****************************************************************)
           (* True iff instance r of the Paxos consensus algorithm has     *)
           (* chosen the value v.                                          *)
           (****************************************************************)
           \E b \in Ballot, MS \in Majority : 
             \A ac \in MS : [type |-> "phase2b", ins |-> r, 
                              bal |-> b, val |-> v, acc |-> ac ] \in msgs
     IN  \/ /\ \A r \in RM : Decided(r, "prepared")
            /\ Send([type |-> "Commit"])
         \/ /\ \E r \in RM : Decided(r, "aborted")
            /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>
-----------------------------------------------------------------------------
(***************************************************************************)
(*                             ACCEPTOR ACTIONS                            *)
(***************************************************************************)
Phase1b(acc) ==  
  \E m \in msgs : 
    /\ m.type = "phase1a"
    /\ aState[m.ins][acc].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
    /\ Send([type |-> "phase1b", 
             ins  |-> m.ins, 
             mbal |-> m.bal, 
             bal  |-> aState[m.ins][acc].bal, 
             val  |-> aState[m.ins][acc].val,
             acc  |-> acc])
    /\ UNCHANGED rmState

Phase2b(acc) == 
  /\ \E m \in msgs : 
       /\ m.type = "phase2a"
       /\ aState[m.ins][acc].mbal \leq m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal, 
                  val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState
-----------------------------------------------------------------------------
PCNext ==  \* The next-state action
  \/ \E r \in RM : \/ RMPrepare(r) 
                   \/ RMChooseToAbort(r) 
                   \/ RMRcvCommitMsg(r) 
                   \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ PCDecide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc) 
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following part of the spec is not covered in Lecture 7.  It will be *)
(* explained in Lecture 8.                                                 *)
(***************************************************************************)
PCSpec == PCInit /\ [][PCNext]_<<rmState, aState, msgs>>
  (*************************************************************************)
  (* The complete spec of the Paxos Commit protocol.                       *)
  (*************************************************************************)

THEOREM PCSpec => []PCTypeOK
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert that the Paxos Commit protocol implements the transaction *)
(* commit protocol of module TCommit.  The following statement imports     *)
(* into the current module the definitions from module TCommit, including  *)
(* the definition of TCSpec.                                               *)
(***************************************************************************)

INSTANCE TCommit

THEOREM PCSpec => TCSpec
=============================================================================

\* Modification History
\* Last modified Sat Aug 07 18:50:40 CEST 2021 by rchaves
\* Created Sat Aug 07 18:09:11 CEST 2021 by rchaves
