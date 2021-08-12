---- MODULE MC ----
EXTENDS formal, TLC

\* CONSTANT definitions @modelParameterConstants:0initialBalances
const_1628784813507156000 == 
[acc \in accounts |-> 2]
----

\* CONSTANT definitions @modelParameterConstants:1accounts
const_1628784813507157000 == 
{"Alice", "Bob"}
----

=============================================================================
\* Modification History
\* Created Thu Aug 12 18:13:33 CEST 2021 by rchaves
