---- MODULE MC ----
EXTENDS car_model, TLC

\* INVARIANT definition @modelCorrectnessInvariants:1
inv_157912235918385000 ==
IF engine = "ON" /\ ambient_light = "ON" /\ exterior_bright < 200 /\ key_state /= "IN IGNITION"
 THEN low_beams = 100
 ELSE TRUE
----
=============================================================================
\* Modification History
\* Created Wed Jan 15 21:05:59 WET 2020 by mont3iro
