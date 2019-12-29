----------------------------- MODULE car_model -----------------------------
EXTENDS Integers

VARIABLES engine,key_state,low_beams,day_time,exterior_brigth,ambient_ligth

  (* Invariante de correção dos tipos                                      *)
TPTypeOK ==  
    /\ engine          \in {"ON","OFF"}
    /\ key_state       \in {"INSERTED","NOT INSERTED","IN IGNITION"}
    /\ low_beams       \in {"ON","OFF","AUTO"}
    /\ day_time        \in {"ON","OFF"}
    /\ exterior_brigth \in {">250LX","<200LX"}
    /\ ambient_ligth   \in {"ON","OFF"}

(* Pedicado de inicialização do sistema                                     *)
Init == 
    /\ engine          = "OFF"
    /\ key_state       = "NOT INSERTED"
    /\ low_beams       = "OFF"
    /\ day_time        = "OFF"
    /\ exterior_brigth = "OFF"
    /\ ambient_ligth   = "OFF"


(* Pedicado que permite inserir a chave                                     *)
InsertKey == 
    /\ key_state        = "NOT INSERTED"
    /\ key_state'       = "INSERTED"
    /\ low_beams'       = low_beams
    /\ day_time'        = day_time
    /\ exterior_brigth' = exterior_brigth
    /\ ambient_ligth'   = ambient_ligth

(* Pedicado que permite a evolução do sistema                               *)
Next == 
    \/ InsertKey
    
(*                      Propriedades        
Permitem aplicar varios estados iniciais e as acções next e o que elas implicam
é obrigatorio para permitir o stur+tering equivalenrte ao skip _<<M,N,m,r,n>> 
*)

Spec == Init /\ [][Next]_<<engine,key_state,low_beams,day_time,exterior_brigth,ambient_ligth>> /\ WF_<<engine,key_state,low_beams,day_time,exterior_brigth,ambient_ligth>>(Next)

=============================================================================
\* Modification History
\* Last modified Sun Dec 29 19:25:47 WET 2019 by macz
\* Created Sun Dec 29 16:17:48 WET 2019 by macz
