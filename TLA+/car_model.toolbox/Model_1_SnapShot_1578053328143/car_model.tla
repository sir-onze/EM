----------------------------- MODULE car_model -----------------------------
EXTENDS Integers

VARIABLES engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary

  (* Invariante de correção dos tipos                                      *)
TPTypeOK ==  
    /\ engine          \in {"ON","OFF"}
    /\ key_state       \in {"INSERTED","NOT INSERTED","IN IGNITION"}
    /\ rotary          \in {"ON","OFF","AUTO"}
    /\ low_beams       \in 0..100
    /\ day_time        \in {"ON","OFF"}
    /\ exterior_bright \in 0..500
    /\ ambient_light   \in {"ON","OFF"}

(* Pedicado de inicialização do sistema                                     *)
Init == 
    /\ engine          = "OFF"
    /\ key_state       = "NOT INSERTED"
    /\ rotary          = "ON"
    /\ low_beams       = 0
    /\ day_time        = "OFF"
    /\ exterior_bright \in 0..500
    /\ ambient_light   = "OFF"


(* Pedicado que permite inserir a chave                                     *)
InsertKey == 
    /\ key_state        = "NOT INSERTED"
    /\ key_state'       = "INSERTED"
    /\ engine'          = engine
    /\ rotary'          = rotary
    /\ low_beams'       = low_beams
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light


IgnitionOn ==
    /\ key_state        = "INSERTED"
    /\ key_state'       = "IN IGNITION"
    /\ IF rotary = "ON"
        THEN /\ low_beams'       = 100
        ELSE /\ IF rotary = "AUTO" /\ exterior_bright < 200
                 THEN /\ low_beams'       = 100
                 ELSE /\ IF rotary = "AUTO" /\ exterior_bright > 250
                          THEN /\ low_beams'       = 0
                          ELSE /\ low_beams'        = low_beams
    /\ engine'          = engine
    /\ rotary'          = rotary
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    
RemoveKey ==
    /\ key_state        = "INSERTED"
    /\ engine           = "OFF"
    /\ key_state'       = "NOT INSERTED"
    /\ rotary'          = rotary
    /\ low_beams'       = low_beams
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    

(* Pedicado que permite a evolução do sistema                               *)
Next == 
    \/ InsertKey
    \/ IgnitionOn
    \/ RemoveKey
    
(*                      Propriedades        
Permitem aplicar varios estados iniciais e as acções next e o que elas implicam
é obrigatorio para permitir o stur+tering equivalenrte ao skip _<<M,N,m,r,n>> 
*)

Spec == Init /\ [][Next]_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>> /\ WF_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>>(Next)

=============================================================================
\* Modification History
\* Last modified Fri Jan 03 12:08:37 WET 2020 by macz
\* Last modified Tue Dec 31 06:21:35 WET 2019 by mont3iro
\* Created Sun Dec 29 16:17:48 WET 2019 by macz