---- MODULE MC ----
EXTENDS formal, TLC

\* CONSTANT definitions @modelParameterConstants:0initialBalances
const_1628458864114151000 == 
[acc \in accounts |-> 2]
----

\* CONSTANT definitions @modelParameterConstants:1accounts
const_1628458864114152000 == 
{"Alice", "Bob"}
----

=============================================================================
\* Modification History
\* Created Sun Aug 08 23:41:04 CEST 2021 by rchaves
