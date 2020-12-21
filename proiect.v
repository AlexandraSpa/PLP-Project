Require Import String.
Open Scope string_scope.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Compute eqb_string "A" "A".


(* Environment *)

Inductive Value :=
| undef : Value
| nat_value : nat -> Value
| bool_val : bool -> Value.

Coercion nat_value : nat >-> Value. 

Scheme Equality for Value.

Inductive Variables :=
| simple: string -> Variables
| array: string -> nat -> Variables.

Scheme Equality for Variables.

Notation "A '[:' B ']'" := (array A B) (at level 40).
Coercion simple : string >-> Variables.
Compute "a"[: 5].

Definition Env := Variables -> Value.

Definition env0 : Env := 
   fun (s : Variables) => undef.

Compute (env0 "C").

Definition is_declared (x : Variables) (env : Env) :=
 if (Value_beq (env x) undef)
 then false
 else true.

Compute is_declared "C" env0.

Definition update (env : Env)
           (x : Variables) (v : nat) :=
  fun y =>
    if (Variables_beq y x)
    then nat_value v
    else (env y).

Definition env1 := update env0 "n" 10.

Compute env1 "n". 

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Definition env2 := env1 [ 1045 /' "n" ].
Compute (env2 "n").

Definition adress := string -> nat.

(*Exemplu*)
Definition adr : adress :=
   fun (s : string) => 0. 

Compute adr "s".  

Definition adress_env := 
   fun (s : string) => adr s.
Compute (adress_env "s").

Definition array_env := nat -> Value. (* adresa -> valoare*)

(*Exemplu*)
Definition array_val : array_env :=
    fun (adr : nat) => undef.

Definition update_array (a : array_env)
           (adr : nat) (v : nat) :=
  fun y =>
    if (Nat.eqb y adr)
    then nat_value v
    else (a y).

Definition literal := nat -> nat.

Inductive AExp :=
| aliteral : nat -> literal -> AExp
| alambda_call : string -> nat -> AExp
| avar : Variables -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| adif: AExp ->AExp -> AExp
| amul : AExp -> AExp -> AExp.

Notation "f '_(' n ')_'" := (alambda_call f n) (at level 40).
Notation "A '_lit' lit" := (aliteral A lit) (at level 40).
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A -' B" := (adif A B) (at level 48).
Coercion anum : nat >-> AExp.
Coercion avar : Variables >-> AExp.

Compute "f"_( 3 )_.
Definition literal1 : literal :=
   fun (n: nat) => n+3.

Check 3 _lit literal1.
Check (2 +' 3 *' 5).
Check (2 +' 3 *' "n").
Check "a"[:3] +' 5.
Check 3 +'  "a"[:10].


Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).

Inductive Stmt :=
| def : Variables -> nat -> Stmt
| decl : Variables -> Stmt
| decl_lambda_expr : string -> Variables -> AExp -> Stmt
| assignment : string -> AExp -> Stmt
| initializer_list : string -> list nat -> Stmt
| break : Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt
| ifthenelse: BExp -> Stmt -> Stmt -> Stmt
| For : Stmt -> BExp -> Stmt -> Stmt -> Stmt.

Notation "'int' X" := (decl X) (at level 50).
Notation "'auto' s '[=]' x 'Return' S 'End'" := (decl_lambda_expr s x S) (at level 50(*, l at level 9*)).
Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90, right associativity).
Notation "'If' A 'Then' B 'Else' C 'End'" := (ifthenelse A B C)(at level 97).
Notation "'If' A 'Then' B 'End'" := (ifthen A B)(at level 97).
Notation "'For(' A ';;;' B ';;;' C ')Do' D" := (For A B C D )(at level 98).
Notation "'#define' A B" := (def A B) (at level 50, A at level 9).

Definition is_break_on (env: Env) :=
if (Value_beq (env "Break") 0)
then false
else true.

(*Exemplu*)
Definition env3 := update env0 "Break" 0.
Compute is_break_on env3.

Compute #define "MAX" 1000.

Compute For( "i"::=1 ;;; "i"<=' "n" ;;; "i"::= "i" +' 1 )Do
        "sum"::= "sum" +' 1.
Compute int "c".
Compute int "c"[: 5].

(*Totodata, pentru pentru a evita folosirea ghilimelelor de fiecare data,
am definit string-urile folosite in programele de mai jos*)

Definition x : string := "x".
Definition a : string := "a".
Definition n : string := "n".
Definition i : string := "i".
Definition sum := "sum".

Compute 
  #define "MAX" 1000;; 
  auto "f" [=] (x) Return (x +' 3) End;;
  int a[: 2];;
  int n;;
  int i;;
  int sum;;
  sum ::= "f"_( 3 )_;;
  initializer_list a (cons 1 (cons 2 nil));;
  n ::= 1 _lit literal1 ;;
  i ::= a[: 0] ;; 
  sum ::= 0 ;;
  while ( i <=' n ) (
          sum ::= sum +' i ;;
          i ::= i +' 1;;
          break
        );;
  If ( i <=' n ) Then
                     ( sum ::= sum +' i ;;
                     i ::= i +' 1 )
  Else (sum ::= 0)
  End;;
  If ( i <=' n ) Then
                     ( sum ::= sum +' i ;;
                     i ::= i +' 1 )
  End;;
  For( i ::= 2 ;;; i<=' n ;;; i ::= i+'1 )Do
          sum ::= sum +' i.

(* Definition init_list := list nat.
Definition list1 : list nat := cons 1 (cons 2 nil).
Compute list1.

Fixpoint suma (l1 : list nat) : nat :=
match l1 with
| nil => 0
| cons n l => n + (suma l)
end.

Compute suma list1.

Definition adr1 : adress :=
   fun s =>
    if (eqb_string s "a")
    then 1000
    else 0.
Compute adr1 "a".

Definition array_val1 := update_array array_val 1000 1.
Compute array_val1 1000.

Fixpoint initializer_list<int> (s : string) (adr : nat) (a : array_env) (l : list nat) :=
match l with
| cons n nil => 
| cons n l => a
end *)
