Require Import String.
Open Scope string_scope.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Compute eqb_string "A" "A".


(* Environment *)


Definition Env (A: Type) := string -> A.

Definition env0 {A: Type} (v : A): Env A := 
   fun (s : string) => v.

Compute (env0 false "C").

Definition update {A : Type} (env : Env A)
           (x : string) (v : A) :=
  fun y =>
    if (eqb_string y x)
    then v
    else (env y).


Definition env1 := update (env0 0) "n" 10.

Compute env1 "x".

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Definition env2 := env1 [ 1045 /' "n" ].
Compute (env2 "n").


Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| adif: AExp ->AExp -> AExp
| amul : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A -' B" := (adif A B) (at level 48).
Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.
Check (2 +' 3 *' 5).
Check (2 +' 3 *' "n").


(* Big-step SOS for arithmetic expressions *)


Reserved Notation "A =[ S ]=> N" (at level 60).

Inductive aeval : AExp -> Env nat -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| diff : forall a3 a4 i3 i4 sigma n, 
    a3 =[ sigma ]=> i3 ->
    a4 =[ sigma ]=> i4 ->
    (i4 <= i3) ->
    n = i3 - i4 ->
    a3 -' a4 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Hint Constructors aeval.

Example ex0 : 10 =[ env1 ]=> 10.
Proof.
  apply const.
Qed.

Example ex2' : 2 +' 2 =[ env1 ]=> 4.
Proof.
  eapply add; eauto.
Qed.

Example ex3' : 2 -' 2 =[ env1 ]=> 0.
Proof.
  eapply diff; eauto.
Qed.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).

(* Big-step SOS for boolean expressions *)

Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env nat -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
where "B ={ S }=> B'" := (beval B S B').

Example and_first : band btrue bfalse ={ env1 }=> false.
Proof.
  apply e_andtrue.
  - apply e_true.
  - apply e_false.
Qed.

Example ex5: "n" <=' 11 ={ env1 }=> true.
Proof.
  eapply e_lessthan.
  - eapply var.
  - eapply const.
  - simpl. reflexivity.
Qed.

Inductive Stmt :=
| assignment : string -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse: BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90, right associativity).
Notation "'If' A 'Then' B 'Else' C 'End'" := (ifthenelse A B C)(at level 97).
Notation "'If' A 'Then' B 'End'" := (ifthen A B)(at level 97).
Notation "'For(' A ';;;' B ';;;' C ')Do' D" := (For A B C D )(at level 98).

Compute For( "i"::=1 ;;; "i"<=' "n" ;;; "i"::= "i" +' 1 )Do
        "sum"::= "sum" +' 1.

(* Big-step SOS for statements *)

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).

Inductive eval : Stmt -> Env nat -> Env nat -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_ifthenfalse : forall b s1 sigma,
    b ={ sigma }=> false ->
    (If b Then s1 End) -{ sigma }-> sigma
| e_ifthentrue : forall b s1 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (If b Then s1 End) -{ sigma }-> sigma1
| e_iffalse : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma1 ->
    (If b Then s1 Else s2 End) -{ sigma }-> sigma1
| e_iftrue : forall b s1 s2 sigma sigma1,
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma1 ->
    (If b Then s1 Else s2 End) -{ sigma }-> sigma1
| e_forfalse : forall A cond C D sigma sigma1,
    A -{ sigma }-> sigma1 ->
    cond ={ sigma1 }=> false ->
    ( For( A ;;; cond ;;; C )Do D ) -{ sigma }-> sigma1
| e_fortrue : forall A cond C D sigma sigma1 sigma',
    A -{ sigma }-> sigma1 ->
    cond ={ sigma1 }=> true ->
    ( D ;; For( C ;;; cond ;;; C )Do D ) -{ sigma1 }-> sigma' -> (*De fiecare data evaluez instructiunea for intr un nou environment, determinat de C.*)
    ( For( A ;;; cond ;;; C )Do D ) -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').

(*Mai jos puteti gasi cateva exemple care demonstreaza faptul ca 
un anumit program este evaluat la o stare finala.*)

(*Totodata, pentru pentru a evita folosirea ghilimelelor de fiecare data,
am definit string-urile folosite in programele de mai jos*)

Definition n : string := "n".
Definition i : string := "i".
Definition sum := "sum".

(*exemplu pentru while*)

Definition sum1 :=
  n ::= 1 ;;
  i ::= 1 ;; 
  sum ::= 0 ;;
  while ( i <=' n ) (
          sum ::= sum +' i ;;
          i ::= i +' 1
        ).

Definition state0 := fun (x : string) => 0.
Example eval_sum1 : 
  exists state, sum1 -{ state0 }-> state /\ state sum = 1.
Proof.
  eexists.
  split.
  - unfold sum1.
    * eapply e_seq.
      ** eapply e_assignment; eauto.
      ** eapply e_seq.
        *** eapply e_assignment; eauto.
        *** eapply e_seq.
           **** eapply e_assignment; eauto.
           **** eapply e_whiletrue.
               ***** eapply e_lessthan; eauto.
               ***** eapply e_seq.
                    ****** eapply e_seq.
                          ******* eapply e_assignment; eauto.
                          ******* eapply e_assignment; eauto.
                    ****** eapply e_whilefalse.
                           eapply e_lessthan; eauto.
  - simpl. unfold update. simpl. reflexivity.
Qed.
        
Compute 
  n ::= 1 ;;
  i ::= 1 ;; 
  sum ::= 0 ;;
  If ( i <=' n ) Then
                     ( sum ::= sum +' i ;;
                     i ::= i +' 1 )
  Else (sum ::= 0)
  End.

(*exemplu pentru ifthenelse*)

Definition sum2 := 
  n ::= 1 ;;
  i ::= 1 ;; 
  sum ::= 0 ;;
  If ( i <=' n ) Then
                     ( sum ::= sum +' i ;;
                     i ::= i +' 1 )
  Else (sum ::= 0)
  End.

Example eval_sum2 :  
  exists state, sum2 -{ state0 }-> state /\ state sum = 1.
Proof.
     eexists.
     split.
     - unfold sum2.
      * eapply e_seq.
       ** eapply e_assignment; eauto.
       ** eapply e_seq.
          *** eapply e_assignment; eauto.
          *** eapply e_seq.
             **** eapply e_assignment; eauto.
             **** eapply e_iftrue.
                 ***** eapply e_lessthan; eauto.
                 ***** eapply e_seq.
                      ****** eapply e_assignment; eauto.
                      ****** eapply e_assignment; eauto.
     - simpl. unfold update. simpl. reflexivity.
Qed.

(*exemplu pentru ifthen*)

Definition sum3 := 
  n ::= 1 ;;
  i ::= 1 ;; 
  sum ::= 0 ;;
  If ( i <=' n ) Then
                     ( sum ::= sum +' i ;;
                     i ::= i +' 1 )
  End.

Example eval_sum3 :  
  exists state, sum3 -{ state0 }-> state /\ state sum = 1.
Proof.
   eexists.
   split.
   - unfold sum3.
     * eapply e_seq.
       ** eapply e_assignment; eauto.
       ** eapply e_seq.
         *** eapply e_assignment; eauto.
         *** eapply e_seq.
            **** eapply e_assignment; eauto.
            **** eapply e_ifthentrue.
                ***** eapply e_lessthan; eauto.
                ***** eapply e_seq.
                     ****** eapply e_assignment; eauto.
                     ****** eapply e_assignment; eauto.
   - simpl. unfold update. simpl. reflexivity.
Qed.

(*exemplu pentru e_forfalse*)

Definition sum4 :=
  n ::= 1 ;; 
  sum ::= 0 ;;
  For( i ::= 2 ;;; i<=' n ;;; i ::= i+'1 )Do
          sum ::= sum +' i.


Example eval_sum4 :  
  exists state, sum4 -{ state0 }-> state /\ state sum = 0.
Proof.
    eexists.
    split.
    - unfold sum4.
     * eapply e_seq.
      ** eapply e_assignment; eauto.
      ** eapply e_seq.
         *** eapply e_assignment; eauto.
         *** eapply e_forfalse.
            **** eapply e_assignment; eauto.
            **** eapply e_lessthan; eauto.
   - unfold update. simpl. reflexivity.
Qed.

(*exemplu pentru e_fortrue*)

Definition sum5 :=
  n ::= 1 ;; 
  sum ::= 0 ;;
  For( i ::= 1 ;;; i<=' n ;;; i ::= i+'1 )Do
          sum ::= sum +' i.

Example eval_sum5 : 
  exists state, sum5 -{ state0 }-> state /\ state sum = 1.
Proof.
  eexists.
  split.
  - unfold sum5.
   * eapply e_seq.
    ** eapply e_assignment; eauto.
    ** eapply e_seq.
      *** eapply e_assignment; eauto.
      *** eapply e_fortrue.
         **** eapply e_assignment; eauto.
         **** eapply e_lessthan; eauto.
         **** eapply e_seq; eauto.
             ***** eapply e_assignment; eauto.
             ***** eapply e_forfalse.
                  ****** eapply e_assignment; eauto.
                  ****** eapply e_lessthan; eauto.
  - simpl. unfold update. simpl. reflexivity.
Qed.


         





















