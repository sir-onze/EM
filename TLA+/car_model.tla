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
    /\ IF ambient_light = "ON"
        THEN /\ IF exterior_bright < 200
                 THEN /\ low_beams' = 100
                 ELSE /\ low_beams' = low_beams
        ELSE /\ IF rotary /= "ON"
                 THEN /\ low_beams' = 0
                 ELSE /\ low_beams' = 50        
    /\ engine'          = engine
    /\ rotary'          = rotary
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
 
 
IgnitionOff ==
    /\ key_state        = "IN IGNITION"
    /\ key_state'       = "INSERTED"
    /\ engine           = "OFF"
    /\ IF ambient_light = "ON"
        THEN /\ IF exterior_bright < 200
                 THEN /\ low_beams' = 100
                 ELSE /\ low_beams' = low_beams
        ELSE /\ IF rotary /= "ON"
                 THEN /\ low_beams' = 0
                 ELSE /\ low_beams' = 50        
    /\ engine'          = engine
    /\ rotary'          = rotary
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    
    
EngineOn ==
    /\ key_state        = "IN IGNITION"
    /\ engine           = "OFF"
    /\ engine'          = "ON"
    /\ IF day_time = "ON" /\ ambient_light = "OFF"
        THEN /\ low_beams' = 100
        ELSE /\ low_beams' = low_beams
    /\ key_state'       = key_state
    /\ rotary'          = rotary
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    

EngineOff ==
    /\ engine           = "ON"
    /\ key_state        = "IN IGNITION"
    /\ key_state'       = "INSERTED"
    /\ engine'           = "OFF"
    /\ IF ambient_light = "ON"
        THEN /\ IF exterior_bright < 200
                 THEN /\ low_beams' = 100
                 ELSE /\ low_beams' = low_beams
        ELSE /\ IF rotary /= "ON"
                 THEN /\ low_beams' = 0
                 ELSE /\ low_beams' = 50
    /\ rotary'          = rotary
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    

    
RemoveKey ==
    /\ key_state        = "INSERTED"
    /\ engine           = "OFF"
    /\ key_state'       = "NOT INSERTED"
    /\ engine'          = engine
    /\ rotary'          = rotary
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ IF ambient_light = "ON" /\ exterior_bright < 200
        THEN /\  low_beams' = 100
        ELSE /\  low_beams' = 0
    /\ ambient_light' = ambient_light

    
RotaryAuto == 
    /\ rotary           /= "AUTO"
    /\ rotary'          = "AUTO"
    /\ IF key_state /= "IN IGNITION"
        THEN /\ low_beams' = 0
        ELSE /\ IF exterior_bright < 200
                 THEN /\ low_beams' = 100
                 ELSE /\ IF exterior_bright > 250 
                                   THEN /\ low_beams' = 0
                                   ELSE /\ low_beams'  = low_beams
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light

                            
RotaryOn == 
    /\ rotary /= "ON"
    /\ rotary' = "ON"
    /\ IF ambient_light = "OFF"  
        THEN /\ IF key_state = "INSERTED" 
                 THEN /\ low_beams' = 50
                 ELSE /\ low_beams' = 100                   
        ELSE /\ IF key_state /= "IN IGNITION"
                 THEN /\ IF exterior_bright < 200
                          THEN /\ low_beams' = 100
                          ELSE /\ low_beams' = low_beams
                 ELSE /\ low_beams' = low_beams     
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    
DaytimeOn ==
    /\ day_time = "OFF" 
    /\ day_time' = "ON"
    /\ IF engine = "ON" /\ rotary = "OFF"
        THEN low_beams' = 100
        ELSE low_beams'  = low_beams
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ rotary'          = rotary
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light

DaytimeOff ==
    /\ day_time  = "ON" 
    /\ day_time' = "OFF"
    /\ IF rotary = "OFF" /\ ambient_light = "OFF"
        THEN low_beams' = 0
        ELSE low_beams'  = low_beams
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ rotary'          = rotary
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
                
(* Pedicado que permite a evolução do sistema                               *)
Next == 
    \/ InsertKey
    \/ IgnitionOn
    \/ EngineOn
    \/ RemoveKey
    \/ RotaryAuto
    \/ RotaryOn
    \/ IgnitionOff
    \/ EngineOff
    \/ DaytimeOn
    \/ DaytimeOff
(*                      Propriedades        
Permitem aplicar varios estados iniciais e as acções next e o que elas implicam
é obrigatorio para permitir o stur+tering equivalenrte ao skip _<<M,N,m,r,n>> 
*)

Spec == Init /\ [][Next]_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>> /\ WF_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>>(Next)

=============================================================================
\* Modification History
\* Last modified Fri Jan 10 22:44:39 WET 2020 by mont3iro
\* Last modified Sun Dec 29 19:25:47 WET 2019 by macz
\* Created Sun Dec 29 16:17:48 WET 2019 by macz

