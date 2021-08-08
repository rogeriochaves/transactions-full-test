------------------------------- MODULE formal -------------------------------

EXTENDS Integers, Sequences

VARIABLE accounts, initialBalances, balances, msgs

Init == accounts = {"Alice", "Bob"}
     /\ initialBalances = [acc \in accounts |-> 10]
     /\ balances = initialBalances
     /\ msgs = {}

DbUpdate == msgs /= {}
            /\ LET msg == CHOOSE msg \in msgs : TRUE
               IN msgs' = msgs \ {msg}
               /\ balances' = [ balances EXCEPT ![msg.account] = msg.amount ]
               /\ UNCHANGED <<accounts, initialBalances>>
            
TransferMoney(from, to, amount) == balances[from] - amount >= 0 (* Account needs to have enough balance, from property testing *)
                                /\ msgs' = msgs \union { [ account |-> from, amount |-> balances[from] - amount ],
                                                         [ account |-> to, amount |-> balances[to] + amount ] }
                                /\ UNCHANGED <<accounts, initialBalances, balances>>

Next == DbUpdate
     \/ \E acc \in accounts:
           balances[acc] > 0 /\ \E amount \in 1..balances[acc] : (* Send only positive integers, from property testing *)
             TransferMoney("Alice", "Bob", amount)

(***************************************************************************)
(*                                INVARIANTS                               *)
(***************************************************************************)

TypeOK == msgs \subseteq [ account : accounts, amount : Int (* Amount has to be an integer, from static typing *) ]

BalancesAlwaysPositive == \A acc \in accounts : balances[acc] >= 0

TotalMoneyStable == LET Sum(balance) == [x, y \in accounts |-> balance[x] + balance[y]]
                    IN Sum(initialBalances) = Sum(balances)

=============================================================================
\* Modification History
\* Last modified Sun Aug 08 19:57:50 CEST 2021 by rchaves
\* Created Sat Aug 07 23:59:18 CEST 2021 by rchaves
