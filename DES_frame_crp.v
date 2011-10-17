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
Inductive sensitivity := secure | normal.
(* Definition signal := nat -> value.  obsolete *)

(*Section Bus_Signals.*)
Section crp.

Definition bus_value := list value.
Definition bus := nat -> (bus_value * sensitivity).

Check bus.

Definition VDD : bus := fun t : nat => (hi::nil, normal).
Definition GND : bus := fun t : nat => (lo::nil, normal).

Definition sliceA (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => match (b t) with
                 | (bv, secure) => (firstn (p2-p1+1) (skipn (p1-1) bv), secure)
                 | (bv, normal) => (firstn (p2-p1+1) (skipn (p1-1) bv), normal)
                 end.

Definition sliceD (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => match (b t) with
                 | (bv, secure) => (rev (firstn (p1-p2+1) (skipn p2 (rev bv))), secure)
                 | (bv, normal) => (rev (firstn (p1-p2+1) (skipn p2 (rev bv))), normal)
                 end.


Definition v := lo::lo::hi::hi::lo::nil.

Definition b := fun t:nat => (v, secure).
Definition b2 := fun t:nat => (v, normal).

Eval compute in sliceA b 1 3.


Eval compute in sliceD b2 4 0.

(* Notation "b @( m , n ) " := (bus_slice b m n ) (at level 50, left associativity). *)
Notation "b [ m , n ] " := (sliceD b m n ) (at level 50, left associativity).
Notation "b @ [ m , n ] " := (sliceA b m n ) (at level 50, left associativity).


Eval compute in  (b [4,1] [3,2]).
Eval compute in (b @[1,4] [3,2]).

Definition bus_length (b : bus) :=
  fun t : nat => length (fst (b t)).
                 

Eval compute in (bus_length (b2)).

Definition not (a : value) : value :=
  match a with
  | lo => hi
  | hi => lo
  end.

(* BUS OPERATION. Ubiqutous calculation. *)
Fixpoint bv_bit_not (a : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => (not la) :: (bv_bit_not a')
  end.

Definition bus_bit_not (b : bus) : bus :=
  fun t:nat => (bv_bit_not (fst (b t)), snd (b t)).

Eval compute in b2[3,1].
Eval compute in bus_bit_not (b2[3,1]).

Definition v2 := lo::hi::lo::lo::lo::nil.
Definition b3 := fun t:nat => (v2, normal).

Definition uoptag (a : sensitivity) : sensitivity := a.
Definition boptag (a b : sensitivity) : sensitivity := 
  match a with
  | secure => secure
  | normal => match b with 
              | secure => secure
              | normal => normal
              end
  end.

Definition rmtag (a : sensitivity) : sensitivity := normal.

Definition xor (a b : value) := match a with
                                | lo => match b with
                                        | lo => lo
                                        | hi => hi end
                                | hi => match b with
                                        | lo => hi
                                        | hi => lo end
                                end.

Fixpoint bv_bit_xor (a b : bus_value) {struct a} := 
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (xor la lb) :: (bv_bit_xor a' b')
                end
  end.    (* here we assume the bus widths are the same *)

Definition bus_bit_xor (a b : bus) : bus :=
  fun t:nat => (bv_bit_xor (fst (a t)) (fst (b t)), boptag (snd (a t)) (snd (b t))).
  

Eval compute in bus_bit_xor (b2[2,1]) (b3[3,2]).
Eval compute in bus_bit_xor (b[2,1]) (b3[3,2]).

Definition and (a b : value) : value :=
  match a with
  | lo => lo
  | hi => match b with
          | lo => lo
          | hi => hi
          end
  end.

Fixpoint bv_bit_and  (a b : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (and la lb) :: (bv_bit_and a' b')
                end
  end.

Definition bus_bit_and (a b : bus) : bus :=
  fun t:nat => (bv_bit_and (fst (a t)) (fst (b t)), boptag (snd (a t)) (snd (b t))).


Eval compute in (b 1).
Eval compute in b2.

Eval compute in bus_bit_and b2 b3.
Eval compute in bus_bit_and b2 b.

Definition or (a b : value) :=
  match a with
  | lo => match b with
          | lo => lo
          | hi => hi end
  | hi => hi
  end.

Fixpoint bv_bit_or (a b : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (or la lb) :: (bv_bit_or a' b')
                end
  end.

Definition bus_bit_or (a b : bus) : bus :=
  fun t:nat => (bv_bit_or (fst (a t)) (fst (b t)), boptag (snd (a t)) (snd (b t))).

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

Definition sen_eq (a b : sensitivity) : value :=
  match a with
  | secure => match b with 
              | secure => hi
              | normal => lo
              end
  | normal => match b with
              | secure => lo
              | normal => hi
              end
  end.

Definition bus_eq (a b : bus) (t : nat) : value :=
  and (bv_eq (fst (a t)) (fst (b t))) (sen_eq (snd (a t)) (snd (b t))).

Eval compute in bus_eq b2 b2.

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
  bv_lt (fst (a t)) (fst (b t)).    (* Here we assume that the tag of comparison buses are the same. *)

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
  bv_gt (fst (a t)) (fst (b t)).  (* Here we assume that the tag of comparison buses are the same. *)

Fixpoint bv_eq_0 (a : bus_value) {struct a} : value :=
  match a with
  | hi :: lt => lo
  | lo :: lt => bv_eq_0 lt
  | nil => hi
  end.

Definition bus_eq_0 (a : bus) (t : nat) : value :=
  bv_eq_0 (fst (a t)).   (* Here the sensitivity of the bus does not matter. *)

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
  intros. unfold bus_eq. unfold sen_eq. destruct (a t). simpl.
  destruct s. rewrite bv_eq_refl; trivial. rewrite bv_eq_refl; trivial.
Qed.
  
Lemma bus_eq_assign : forall (t : nat) (a b : bus), a = b -> (bus_eq a b t) = hi.
Proof.
  intros. rewrite H. apply bus_eq_refl.
Qed.

(*End Bus_Signals.


Section Expressions.*)

Inductive expr :=
  | econv : bus_value -> expr
  | econb : bus -> expr
  | eand : expr -> expr -> expr
  | eor : expr -> expr -> expr
  | exor : expr -> expr -> expr
  | enot : expr -> expr
  | cond : expr -> expr -> expr -> expr
  | perm : expr -> expr (* newly modified in DES_frame_crp.v to deal with signals combinations. *)
  | sbox : bus -> expr  (* newly added in DES_frame_crp.v to deal with sbox operation. *)
  | eq : expr -> expr -> expr
  | lt : expr -> expr -> expr
  | gt : expr -> expr -> expr
  | case3 : expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr.

Fixpoint eval (e : expr) (t : nat) {struct e} : bus_value*sensitivity :=
  match e with
  | econv v => (v, normal)
  | econb b => b t
  | eand ex1 ex2 => (bv_bit_and (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | eor ex1 ex2 => (bv_bit_or (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | exor ex1 ex2 => (bv_bit_xor (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | enot ex => (bv_bit_not (fst (eval ex t)), uoptag (snd (eval ex t)))
  | cond cex ex1 ex2 => match (bv_eq_0 (fst (eval cex t))) with
                        | hi => eval ex1 t
                        | lo => eval ex2 t end
  | perm ex => (fst (eval ex t), normal)
  | sbox b => (b t)
  | eq ex1 ex2 => match (bv_eq (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => (hi :: nil, normal)
                  | lo => (lo :: nil, normal) end
  | lt ex1 ex2 => match (bv_lt (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => (hi :: nil, normal)
                  | lo => (lo :: nil, normal) end
  | gt ex1 ex2 => match (bv_gt (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => (hi :: nil, normal)
                  | lo => (lo :: nil, normal) end
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>     
                  match fst (eval sel t) with
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

Definition expr_sen (e : expr) (t : nat) : sensitivity :=
  snd (eval e t).

Definition bus_sen (b : bus) (t : nat) : sensitivity :=
  snd (eval (econb b) t).

(*End Expressions.


Section code_expressions.*)

Inductive code :=
  | outb : bus -> code
  | inb : bus -> code
  | wireb : bus -> code
  | regb : bus -> code
  | assign_ex : bus -> expr -> code
  | assign_b : bus -> bus -> code
  (*| perm_b : bus -> code*)
  | assign_case3 : bus -> expr -> code
  | codepile : code -> code -> code.

Notation " c1 ; c2 " := (codepile c1 c2) (at level 50, left associativity).

(* Let's only consider the case that each module only contains one output bus.
It holds for all modules in DES example. 
Or more precisely, return the sensitivity of the specific bus (manually iterate. *)
Fixpoint chk_code_sen (c : code) (t : nat) : sensitivity :=
  match c with
  | outb b => normal
  | inb b => normal
  | wireb b => normal
  | regb b => normal
  | assign_ex b ex => expr_sen ex t
  | assign_b b1 b2 => bus_sen b2 t
  | assign_case3 b ex => expr_sen ex t
  | codepile c1 c2 => boptag (chk_code_sen c1 t) (chk_code_sen c2 t)
  end.
  
(*End code_expressions.


Section Sub_Module_key_selh.*)
(* a.k.a. RTL code file *)

Variables P R K_sub : bus.
Variables E X S : bus.

Axiom secret_K_sub : forall (t : nat), bus_sen K_sub t = secure.


Definition crp : code :=
  outb P;
  inb R;
  inb K_sub;
  wireb E;
  wireb X;
  wireb S;
  assign_ex E (perm (econb R));
  assign_ex P (perm (sbox (bus_bit_xor E K_sub))).
  



Theorem no_leaking_crp : forall (t : nat), chk_code_sen crp t = normal.
Proof.
  intros. unfold chk_code_sen. unfold crp.
  unfold expr_sen. unfold eval. simpl. reflexivity.
Qed.




End crp.


