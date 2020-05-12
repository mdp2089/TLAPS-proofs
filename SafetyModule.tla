---------------------------- MODULE MDP_SM_temp ----------------------------

EXTENDS Naturals, TLAPS

CONSTANT Pos, Tt, Rst, RP, Pos0, Nschk, Npchk, ValidT, EmptyT, IsInside, Getcmd, Takeact, ClosestRP
VARIABLES Pcmd, T, Rs, tm, l, L, y

ASSUME Asmp1 == /\ Pos0 \in Pos
                /\ Nschk \in [Tt -> BOOLEAN]
                /\ Npchk \in [Rst -> BOOLEAN]
                /\ ValidT \in [Tt -> BOOLEAN]
                /\ EmptyT \in [Tt -> BOOLEAN]
                /\ IsInside \in [Pos -> BOOLEAN]
                /\ Getcmd \in [Tt -> Pos]
                /\ Takeact \in [Nat -> BOOLEAN]
                /\ ClosestRP \in [Pos -> RP]
                /\ RP \in SUBSET Pos

ASSUME Asmp2 == \A i \in RP : IsInside[i]

Nrtc == /\ ValidT[T] 
        /\ IsInside[Getcmd[T]]

TypeInv == /\ T \in Tt 
           /\ Rs \in Rst 
           /\ tm \in Nat 
           /\ y \in Pos 
           /\ L \in Nat 
           /\ l \in Nat
           /\ Pcmd \in Pos
                      
Nsm1 == /\ Takeact[tm] 
        /\ EmptyT[T] 
        /\ 9*L <= 10*l  
        /\ tm' = tm+1 
        /\ Pcmd' = ClosestRP[y]

Nsm2 == /\ Takeact[tm]
        /\ EmptyT[T] 
        /\ 9*L > 10*l  
        /\ tm' = tm+1 
        /\ Pcmd' = Pos0

Nsm3 == /\ Takeact[tm] 
        /\ ~EmptyT[T] 
        /\ Nschk[T] 
        /\ Npchk[Rs]
        /\ Nrtc 
        /\ tm' = tm+1 
        /\ Pcmd' = Getcmd[T]

Nsm4 == /\ Takeact[tm] 
        /\ ~EmptyT[T] 
        /\ ~Nschk[T] \/ ~Npchk[Rs] \/ ~Nrtc
        /\ 9*L <= 10*l  
        /\ tm' = tm+1 
        /\ Pcmd' = ClosestRP[y]

Nsm == \/ Nsm1
       \/ Nsm2
       \/ Nsm3
       \/ Nsm4
       
Initsm == /\ tm = 1 
          /\ Pcmd = Getcmd[T]
          /\ ValidT[T] 
          /\ IsInside[Pcmd]
          /\ Pcmd \in Pos
          /\ tm \in Nat
                 
Varssm == <<tm,Pcmd>>
Varsesm == <<T,Rs,y,l,L>>       

Initesm == /\ T \in Tt
           /\ Rs \in Rst
           /\ y \in Pos 
           /\ L \in Nat 
           /\ l \in Nat
           
Nesm == /\ T' \in Tt
        /\ Rs' \in Rst
        /\ y' \in Pos 
        /\ L' \in Nat 
        /\ l' \in Nat
           
Npsm == \/ Pcmd = Pos0
        \/ IsInside[Pcmd]
           
SM_sys == Initsm /\ [][Nsm]_Varssm /\ WF_Varssm(Nsm)
SM_env == Initesm /\ [][Nesm]_Varsesm 
SM_prop == []Npsm
              
LEMMA TypeCorrectness == SM_env /\ SM_sys => []TypeInv 
<1>1. Initsm /\ Initesm => TypeInv
BY DEF Initsm, Initesm, TypeInv
<1>2. TypeInv /\ [Nsm]_Varssm /\ [Nesm]_Varsesm => TypeInv'
BY Asmp1 DEF TypeInv, Nrtc, Nsm, Nesm, Varssm, Varsesm, Nsm1, Nsm2, Nsm3, Nsm4
<1>. QED BY <1>1, <1>2, PTL DEF SM_env, SM_sys

THEOREM Main == SM_env /\ SM_sys => SM_prop
<1>1. Initsm /\ Initesm => Npsm
   BY Asmp1, Asmp2 DEF Initsm, Initesm, Npsm
<1>2. TypeInv /\ Npsm /\ [Nsm]_Varssm /\ [Nesm]_Varsesm => Npsm'
   BY Asmp1, Asmp2 DEF TypeInv, Nrtc, Nsm, Nesm, Varssm, Varsesm, Nsm1, Nsm2, Nsm3, Nsm4, Npsm
<1>. QED BY <1>1, <1>2, PTL, TypeCorrectness DEF SM_env, SM_sys, SM_prop
  
(*LEMMA Initsm /\ Initesm => Npsm 
BY Asmp1, Asmp2 DEF Initsm, Initesm, Npsm
  
LEMMA TypeInv /\ TypeInv' /\ Npsm /\ Nsm4 /\ Nesm => Npsm' 
BY Asmp1, Asmp2 DEF TypeInv, Nrtc, Nsm, Nesm, Varssm, Varsesm, Nsm1, Nsm2, Nsm3, Nsm4, Npsm
  
LEMMA Npsm /\ TypeInv /\ TypeInv' /\ [Nsm]_Varssm /\ [Nesm]_Varsesm => Npsm'
BY Asmp1, Asmp2 DEF TypeInv, Nrtc, Nsm, Nesm, Varssm, Varsesm, Nsm1, Nsm2, Nsm3, Nsm4, Npsm

LEMMA Npsm /\ TypeInv /\ [Nsm]_Varssm /\ [Nesm]_Varsesm => Npsm'
BY Asmp1, Asmp2 DEF TypeInv, Nrtc, Nsm, Nesm, Varssm, Varsesm, Nsm1, Nsm2, Nsm3, Nsm4, Npsm*)
  
=============================================================================

