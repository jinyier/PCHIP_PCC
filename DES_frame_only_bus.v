(* A new framework to redefine the Verilog-Coq semantics model.
The BUS definition is re-designed from my previous work not to explicitly 
include D or A appendix. *)

(* In order to label and track the information flow within the circuit and within 
each module/sub-module, I need to define two types of bus: bus (normal buses) and
s_bus (secure bus). Only permutation calculation would remove the secure tag of 
internal information. The secure tag for top module is predefined (negotiated between
proof writer and users/designers). 
As the frist step towards information flow tracking, the secure tag for sub-module is
also predefined. For example, for "key_selh", the secure tag is only added on 'K'. 
All outputs of modules/sub-modules should be normal signals with the secure tags removed.
*)


Require Import Bool Arith List.
Require Omega.

Inductive value := lo | hi.
Definition signal := nat -> value. (* obsolete *)

Section Bus_Signals.

Definition bus_value := list value.
Definition bus := nat -> bus_value.

Definition VDD : bus := fun t : nat => hi::nil.
Definition GND : bus := fun t : nat => lo::nil.

Definition sliceA (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => firstn (p2-p1+1) (skipn (p1-1) (b t)).

Definition sliceD (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => rev (firstn (p1-p2+1) (skipn p2 (rev (b t)))).


Definition v := lo::lo::hi::hi::lo::nil.

Definition b := fun t:nat => v.
Definition b2 := fun t:nat => v.

Eval compute in sliceA b 1 3.


Eval compute in sliceD b2 4 0.

(* Notation "b @( m , n ) " := (bus_slice b m n ) (at level 50, left associativity). *)
Notation "b [ m , n ] " := (sliceD b m n ) (at level 50, left associativity).
Notation "b @ [ m , n ] " := (sliceA b m n ) (at level 50, left associativity).


Eval compute in  (b [4,1] [3,2]).
Eval compute in (b @[1,4] [3,2]).

Definition bus_length (b : bus) :=
  fun t : nat => length (b t).
                 

Eval compute in (bus_length (b2)).


(* BUS OPERATION. Ubiqutous calculation. *)
Fixpoint bv_bit_not (a : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => (not la) :: (bv_bit_not a')
  end.

Definition bus_bit_not (b : bus) : bus :=
  fun t:nat => bv_bit_not (b t).

Eval compute in b2[3,1].
Eval compute in bus_bit_not (b2[3,1]).

Definition v2 := lo::hi::lo::lo::lo::nil.
Definition b3 := fun t:nat => v2.

Fixpoint bv_bit_xor (a b : bus_value) {struct a} := 
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (xor la lb) :: (bv_bit_xor a' b')
                end
  end.    (* here we assume the bus widths are the same *)

Definition bus_bit_xor (a b : bus) : bus :=
  fun t:nat => bv_bit_xor (a t) (b t).
  

Eval compute in bus_bit_xor (b2[2,1]) (b3[3,2]).

Fixpoint bv_bit_and  (a b : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (and la lb) :: (bv_bit_and a' b')
                end
  end.

Definition bus_bit_and (a b : bus) : bus :=
  fun t:nat => bv_bit_and (a t) (b t).


Eval compute in (b 1).
Eval compute in b2.

Eval compute in bus_bit_and b2 b3.

Fixpoint bv_bit_or (a b : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (or la lb) :: (bv_bit_or a' b')
                end
  end.

Definition bus_bit_or (a b : bus) : bus :=
  fun t:nat => bv_bit_or (a t) (b t).

Eval compute in bus_bit_or b2 b3.

(* Bus comparisons *)
Fixpoint bv_eq (a b : bus_value) {struct a} : value :=
  match a with 
  | nil => hi
  | la :: a' => match b with 
                | nil => hi
                | lb :: b' => match (la, lb) with
                              | (lo, lo) => bv_eq a' b'
                              | (lo, hi) => lo
                              | (hi, lo) => lo
                              | (hi, hi) => bv_eq a' b'
                              end
                end
  end.

Definition bus_eq (a b : bus) (t : nat) : value :=
  bv_eq (a t) (b t).

Eval compute in bus_eq b2 b3.

Fixpoint bv_lt (a b : bus_value) {struct a} :=
  match a with
  | nil => lo
  | la :: a' => match b with
                | nil => lo
                | lb :: b' => match (la, lb) with
                              | (lo, lo) => bv_lt a' b'
                              | (lo, hi) => hi
                              | (hi, lo) => lo
                              | (hi, hi) => bv_lt a' b'
                              end
                end
  end.

Definition bus_lt (a b : bus) (t : nat) : value :=
  bv_lt (a t) (b t).

Eval compute in bus_lt b3 b2.

Fixpoint bv_gt (a b : bus_value) {struct a} :=
  match a with
  | nil => lo
  | la :: a' => match b with
                | nil => lo
                | lb :: b' => match (la, lb) with
                              | (lo, lo) => bv_gt a' b'
                              | (lo, hi) => lo
                              | (hi, lo) => hi
                              | (hi, hi) => bv_gt a' b'
                              end
                 end
  end.

Definition bus_gt (a b : bus) (t : nat) : value :=
  bv_gt (a t) (b t).

Fixpoint bv_eq_0 (a : bus_value) {struct a} : value :=
  match a with
  | hi :: lt => lo
  | lo :: lt => bv_eq_0 lt
  | nil => hi
  end.

Definition bus_eq_0 (a : bus) (t : nat) : value :=
  bv_eq_0 (a t).

Definition v3 := lo::lo::lo::nil.
Definition v4 := lo::nil.
Definition v5 := hi::lo::nil.
Definition v6 := lo::hi::nil.


Eval compute in bv_eq_0 v3.
Eval compute in bv_eq_0 v4.
Eval compute in bv_eq_0 v5.
Eval compute in bv_eq_0 v6.

Eval compute in bus_eq_0 b2 1.


Eval compute in bus_gt b2 b2.

Lemma bv_eq_refl : forall (t : nat) (a : bus_value), (bv_eq a a) = hi.
Proof. 
  intros. unfold bv_eq. induction a. trivial.
  rewrite IHa. destruct a. trivial. trivial.
Qed.

Lemma bus_eq_refl : forall (t : nat) (a : bus), (bus_eq a a t) = hi.
Proof.
  intros. unfold bus_eq. destruct a; apply bv_eq_refl; trivial.
Qed.
  
Lemma bus_eq_assign : forall (t : nat) (a b : bus), a = b -> (bus_eq a b t) = hi.
Proof.
  intros. rewrite H. apply bus_eq_refl.
Qed.

End Bus_Signals.


Section Expressions.

Inductive expr :=
  | econv : bus_value -> expr
  | econb : bus -> expr
  | eand : expr -> expr -> expr
  | eor : expr -> expr -> expr
  | exor : expr -> expr -> expr
  | enot : expr -> expr
  | cond : expr -> expr -> expr -> expr
  | perm : bus -> expr
  | eq : expr -> expr -> expr
  | lt : expr -> expr -> expr
  | gt : expr -> expr -> expr
  | case3 : expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr.

Fixpoint eval (e : expr) (t : nat) {struct e} : bus_value :=
  match e with
  | econv v => v
  | econb b => b t
  | eand ex1 ex2 => bv_bit_and (eval ex1 t) (eval ex2 t)
  | eor ex1 ex2 => bv_bit_or (eval ex1 t) (eval ex2 t)
  | exor ex1 ex2 => bv_bit_xor (eval ex1 t) (eval ex2 t)
  | enot ex => bv_bit_not (eval ex t)
  | cond cex ex1 ex2 => match (bv_eq_0 (eval cex t)) with
                        | hi => eval ex1 t
                        | lo => eval ex2 t end
  | eq ex1 ex2 => match (bv_eq (eval ex1 t) (eval ex2 t)) with
                  | hi => hi :: nil
                  | lo => lo :: nil end
  | lt ex1 ex2 => match (bv_lt (eval ex1 t) (eval ex2 t)) with
                  | hi => hi :: nil
                  | lo => lo :: nil end
  | gt ex1 ex2 => match (bv_gt (eval ex1 t) (eval ex2 t)) with
                  | hi => hi :: nil
                  | lo => lo :: nil end
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>     
                  match eval (econb sel) t with
                  | lo::lo::lo::nil => eval e1 t
                  | lo::lo::hi::nil => eval e2 t
                  | lo::hi::lo::nil => eval e3 t
                  | lo::hi::hi::nil => eval e4 t
                  | hi::lo::lo::nil => eval e5 t
                  | hi::lo::hi::nil => eval e6 t
                  | hi::hi::lo::nil => eval e7 t
                  | hi::hi::hi::nil => eval e8 t
                  | _ => eval e1 t
                  end
  end.

End Expressions.

Section Sub_Module.
(* a.k.a. RTL code file *)

Inductive code :=
  | outb : bus -> code
  | inb : bus -> code
  | wireb : bus -> code
  | regb : bus -> code
  | assign_ex : bus -> expr -> code
  | assign_b : bus -> bus -> code
  | assigns_ex : 
  | assign_case3 : bus -> expr -> code
  | codepile : code -> code -> code.

Notation " c1 ; c2 " := (codepile c1 c2) (at level 50, left associativity).

Variables K_sub K roundSel K1 K2 K3 K4 K5 K6 K7 K8 roundSelH : bus.
Variables decrypt decryptH : bus.

Definition key_selh :=
  outb K_sub;
  inb K......




















