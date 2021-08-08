---- MODULE MC ----
EXTENDS formal, TLC

\* CONSTANT definitions @modelParameterConstants:0initialBalances
const_16284575764501139000 == 
[acc \in accounts |-> 10]
----

\* CONSTANT definitions @modelParameterConstants:1accounts
const_16284575764501140000 == 
{"Alice", "Bob"}
----

=============================================================================
\* Modification History
\* Created Sun Aug 08 23:19:36 CEST 2021 by rchaves
