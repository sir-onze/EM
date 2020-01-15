----------------------------------------------------- MODULE car_model -----------------------------------------------------------
EXTENDS Integers

(*                              Definição dos conceitos base do problema 

    (1) engine -> A modelação que foi feita para simular o estado do motor, ligado On ou não ligado, caso não
    esteja no estado On;
    (2) key_state -> A modelação que foi feita para simular o estado de inserção ou não da chave no carro e a posição na ignição;
    (4) rotary -> A modelação que foi feita para simular o rotary que está no documento analisado, sendo que 
    pode estar no estado ON,não estar no On que para o modelo siginifica estar Off e no Auto
    (5) low beams -> Representam os low beams presentes no documento, pode estar no On ou caso não estejam no
    On, para o modelação feita significa que estão desligados
    (6) day time -> É a representação referida no documento como "daytime  running  light"
    (7) exterior brigth -> A modelação que foi feita para representar os valores obtidos pelos sensores
    de lumninosidade referidos no documento, o estado LX_HIGH representa os valores acima de 250LX e o LX_LOW
    representam os valores inferiores a 200LX 
    (8) ambient light -> É a representação para o termo com o mesmo nome referido no documento
*)

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

(* Invariante que garante a propriedade ELS14 do documento -> Se o rotary estiver ligado e a chave na ignição entao os low_beams tem que
estar a 100%                                    *)
ELS14 == 
    IF rotary = "ON" /\ key_state = "IN IGNITION"
    THEN low_beams = 100
    ELSE TRUE


(* Pedicado de inicialização do sistema                                     *)
Init == 
    /\ engine          = "OFF"
    /\ key_state       = "NOT INSERTED"
    /\ rotary          = "OFF"
    /\ low_beams       = 0
    /\ day_time        = "OFF"
    /\ exterior_bright \in 0..500
    /\ ambient_light   = "OFF"


(* Pedicado que permite inserir a chave e tem em comsideração o extado do rotary e da exterior brigth de maneira a tribuir valores 
diferentes aos low_beams                                    *)
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

(* Pedicado que permite remover a chave  e tem em consideração a ambiente ligth de maneira a ajustar os valores dos low beams
                                    *) 
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


(* Pedicado que permite colocar a chave na posição de ignição tendo em conta o estado do rotary e da exterior brigthness de maneira
a atribuir valores aos low beams no estado seguinte                                 *) 
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
 
(* Pedicado que permite remover a chave na posição de ignição e tem em conta o estado do rotary e da exterior brigthness de maneira
a atribuir valores aos low beams no estado seguinte                                 *) 
  
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
    
(* Pedicado que permite ligar o motor tendo em conta o estado da ambient light de maneira a atribuir um valor ao próximo estado 
dos low beams                            *)  
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
    

(* Pedicado que permite desligar o motor e tem em conta o estado do rotary e da exterior brigthness de maneira
a atribuir valores aos low beams no estado seguinte                                  *)  
EngineOff ==
    /\ engine           = "ON"
    /\ key_state        = "IN IGNITION"
    /\ key_state'       = "INSERTED"
    /\ engine'          = "OFF"
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
    

(* Pedicado que permite passar o Rotary para automático tendo em conta a exterior brigthness e o valor dos low_beams,conjugados
                    *) 
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


(* Pedicado que permite passar o Rotary para On -> ligado tendo em conta o valor da key e exterior brigthness de maneira a atribuir
valores ao próximo estados dos low beams                   *)                   
RotaryOn == 
    /\ rotary /= "ON"
    /\ rotary' = "ON"
    /\ IF ambient_light = "OFF"  
        THEN /\ IF key_state = "INSERTED" 
                 THEN /\ low_beams' = 50
                 ELSE /\ IF key_state = "IN IGNITION"
                          THEN low_beams' = 100
                          ELSE low_beams' = low_beams                   
        ELSE /\ IF key_state /= "IN IGNITION"
                 THEN /\ IF exterior_bright < 200
                          THEN /\ low_beams' = 100
                          ELSE /\ low_beams' = low_beams
                 ELSE low_beams' = 100
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light
    

(* Pedicado que permite passar o Rotary para Off -> desligado tendo em atenção o key state,a exterior brightness, o engine
e o day time de maneira a atribuir o valor dos low beams no proximo estado                  *)      
RotaryOff ==
    /\ rotary /= "OFF"
    /\ rotary' = "OFF"
    /\ IF ambient_light = "ON"
        THEN /\ IF key_state /= "IN IGNITION" /\ exterior_bright < 200
                 THEN /\ low_beams' = 100
                 ELSE /\ low_beams' = 0
        ELSE /\ IF day_time = "ON" /\ engine = "ON"
                 THEN low_beams' = low_beams
                 ELSE low_beams' = 0
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ day_time'        = day_time
    /\ exterior_bright' = exterior_bright
    /\ ambient_light'   = ambient_light

(* Pedicado que permite ativar o dayTime  tendo em conta o valor do engine e do rotary de maneira a atribuir o valor do proximo estado
dos low beams              *)
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

(* Pedicado que permite desativar o dayTime  tendo em conta o valor do rotary e da ambient light                *)
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

(* Pedicado que permite ativar a Ambient ligth tendo em conta o key state e a exterior brigthness                  *)
AmbientOn ==
    /\ ambient_light    = "OFF"
    /\ ambient_light'   = "ON"
    /\ IF key_state /= "IN IGNITION" /\ exterior_bright < 200
        THEN low_beams' = 100
        ELSE low_beams'  = low_beams
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ rotary'          = rotary
    /\ exterior_bright' = exterior_bright
    /\ day_time'        = day_time

(* Pedicado que permite desativar a Ambient ligth conjugando todos os possíveis valores das variáveis referenciadas no documento
que podem causar alterações nos low beams                 *)
AmbientOff ==
    /\ ambient_light    = "ON"
    /\ ambient_light'   = "OFF"
    /\ IF rotary = "ON"
        THEN /\ IF key_state = "INSERTED"
                 THEN /\ low_beams' = 50
                 ELSE /\ IF key_state = "IN IGNITION" 
                       THEN /\ low_beams' = 100
                       ELSE /\ low_beams' = low_beams
        ELSE /\ IF rotary = "AUTO" /\ key_state = "IN IGNITION"
                 THEN /\ IF exterior_bright < 200
                          THEN /\ low_beams' = 100
                          ELSE /\ IF exterior_bright > 250
                                   THEN low_beams' = 0
                                   ELSE low_beams' = low_beams
                 ELSE /\ IF rotary = "AUTO" /\ key_state = "INSERTED"
                          THEN /\ low_beams' = 0
                          ELSE /\ IF rotary = "OFF" /\ day_time = "OFF"
                                   THEN /\ low_beams' = 0
                                   ELSE /\ IF day_time = "ON" /\ engine = "ON"
                                            THEN low_beams' = 100
                                            ELSE low_beams' = low_beams
                                            
                                                          
    /\ engine'          = engine
    /\ key_state'       = key_state
    /\ rotary'          = rotary
    /\ exterior_bright' = exterior_bright
    /\ day_time'        = day_time


     
(* Pedicado que permite a evolução do sistema                               *)
Next == 
    \/ InsertKey
    \/ IgnitionOn
    \/ EngineOn
    \/ RemoveKey
    \/ RotaryAuto
    \/ RotaryOn
    \/ RotaryOff
    \/ IgnitionOff
    \/ EngineOff
    \/ DaytimeOn
    \/ DaytimeOff
    \/ AmbientOn
    \/ AmbientOff
   
(*                      Propriedades        
Permitem aplicar varios estados iniciais e as acções next e o que elas implicam
é obrigatorio para permitir o stur+tering equivalenrte ao skip _<<M,N,m,r,n>> 
*)

Spec == Init /\ [][Next]_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>> /\ WF_<<engine,key_state,low_beams,day_time,exterior_bright,ambient_light,rotary>>(Next)

=============================================================================
\* Modification History
\* Last modified Wed Jan 15 20:05:53 WET 2020 by macz
\* Last modified Wed Jan 15 03:59:24 WET 2020 by mont3iro
\* Created Sun Dec 29 16:17:48 WET 2019 by macz

