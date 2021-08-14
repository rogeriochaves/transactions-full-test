---- MODULE MC ----
EXTENDS formal, TLC

\* CONSTANT definitions @modelParameterConstants:0initialBalances
const_162885458785663000 == 
[acc \in accounts |-> 1]
----

\* CONSTANT definitions @modelParameterConstants:1accounts
const_162885458785664000 == 
{"Alice", "Bob", "Carlos"}
----

=============================================================================
\* Modification History
\* Created Fri Aug 13 13:36:27 CEST 2021 by rchaves
