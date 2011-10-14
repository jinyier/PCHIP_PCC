(* A new framework to redefine the Verilog-Coq semantics model.
The BUS definition is re-designed from my previous work not to explicitly 
include D or A appendix. *)

Require Import Bool Arith List.
Require Omega.

Inductive value := lo | hi.
Definition signal := nat -> value.
Definition VDD : signal := fun t : nat => hi.
Definition GND : signal := fun t : nat => lo.

Section Bus_Signals.

Definition bus_value := list value.
Definition bus := nat -> bus_value.

Definition sliceA (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => firstn (p2-p1+1) (skipn (p1-1) (b t)).

Definition sliceD (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => rev (firstn (p1-p2+1) (skipn p2 (rev (b t)))).

Definition slice (b: bus)(p1 p2:nat):bus :=
  if le_dec p1 p2 then sliceA b p1 p2 else sliceD b p1 p2.


Definition v := lo::lo::hi::hi::lo::nil.

Definition b := fun t:nat => v.
Definition b2 := fun t:nat => v.

Eval compute in slice b 1 3.


Eval compute in slice b2 4 0.

(* Notation "b @( m , n ) " := (bus_slice b m n ) (at level 50, left associativity). *)
Notation "b [ m , n ] " := (slice b m n ) (at level 50, left associativity).
(* Notation "b @ [ m , n ] " := (sliceA b m n ) (at level 50, left associativity). *)


Eval compute in  (b [4,1] [3,2]).
Eval compute in (b [1,4] [3,2]).

Definition bus_length (b : bus) :=
  fun t : nat => length (b t).
                 

Eval compute in (bus_length (b2)).

Definition not (a : value) : value :=
  match a with
  | lo => hi
  | hi => lo
  end.

Eval compute in (not hi).

Definition sig_not (a : signal) : signal :=
  fun t : nat => not (a t).

Definition s := fun t : nat => hi.


Eval compute in (fun t:nat => sig_not s t).


Definition xor (a b : value) := match a with
                                | lo => match b with
                                        | lo => lo
                                        | hi => hi end
                                | hi => match b with
                                        | lo => hi
                                        | hi => lo end
                                end.

Definition sig_xor (a b : signal) :=
  fun t : nat => match (a t) with
                 | lo => match (b t) with
                         | lo => lo
                         | hi => hi end
                 | hi => match (b t) with
                         | lo => hi
                         | hi => lo end
                 end.


Definition and (a b : value) : value :=
  match a with
  | lo => lo
  | hi => match b with
          | lo => lo
          | hi => hi
          end
  end.

Definition sig_and (a b : signal) : signal :=
  fun t : nat => match (a t) with
                 | lo => lo
                 | hi => match (b t) with
                         | lo => lo
                         | hi => hi end
                 end.

Definition nand (a b : value) := not (and a b).
Definition sig_nand (a b : signal) := sig_not (sig_and a b).

Definition or (a b : value) :=
  match a with
  | lo => match b with
          | lo => lo
          | hi => hi end
  | hi => hi
  end.

Definition sig_or (a b : signal) :=
  fun t : nat =>  match a t with
                  | lo => match b t with
                          | lo => lo
                          | hi => hi end
                  | hi => hi
                  end.

Definition nor (a b : value) := not (or a b).
Definition sig_nor (a b : signal) := sig_not (sig_or a b).


(* BUS OPERATION. *)
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
  | econv : value -> expr
  | econs : signal -> expr
  | econb : bus -> expr
  | eand : expr -> expr -> expr
  | eor : expr -> expr -> expr
  | exor : expr -> expr -> expr
  | enot : expr -> expr
  | cond : expr -> expr -> expr -> expr
  | eq : expr -> expr -> expr
  | lt : expr -> expr -> expr
  | gt : expr -> expr -> expr.

Fixpoint eval (e : expr) (t : nat) {struct e} : bus_value :=
  match e with
  | econv v => v :: nil
  | econs s => (s t) :: nil
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
  end.

End Expressions.

Section Sub_Module.
(* a.k.a. RTL code file *)

Inductive code :=
  | outs : signal -> code
  | outb : bus -> code
  | ins : signal -> code
  | inb : bus -> code
  | wires : signal -> code
  | wireb : bus -> code
  | regs : signal -> code
  | regb : bus -> code
  | assignb_ex : bus -> expr -> code
  | assignb_b : bus -> bus -> code
  | case3 : bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> code
  | codepile : code -> code -> code.

Notation " c1 ; c2 " := (codepile c1 c2) (at level 50, left associativity).

Variables K_sub K roundSel K1 K2 K3 K4 K5 K6 K7 K8 roundSelH : bus.
Variables decrypt decryptH : bus.

Definition key_selh :=
  outb K_sub;
  inb K.

Definition eval_caseb3 (c : caseblockb3) (t : nat) : bus_value :=
  match c with
  | cb a sel b1 b2 b3 b4 b5 b6 b7 b8 =>
                  match eval (econb sel) t with
                  | lo::lo::lo::nil => eval (econb (assign_b a b1)) t
                  | lo::lo::hi::nil => eval (econb (assign_b a b2)) t
                  | lo::hi::lo::nil => eval (econb (assign_b a b3)) t
                  | lo::hi::hi::nil => eval (econb (assign_b a b4)) t
                  | hi::lo::lo::nil => eval (econb (assign_b a b5)) t
                  | hi::lo::hi::nil => eval (econb (assign_b a b6)) t
                  | hi::hi::lo::nil => eval (econb (assign_b a b7)) t
                  | hi::hi::hi::nil => eval (econb (assign_b a b8)) t
                  | _ => eval (econb (assign_b a b1)) t
                  end
  end.


Section Bus_Assignment.

(* ??? *)
Definition assign_ex (e : expr) : bus :=
(*  forall t : nat, (b t) = (eval e t). *)
  eval e.

Lemma assign_eq : forall (a : bus) (e : expr) (t : nat), a = (assign_ex e) -> (a t) = (eval e t).
Proof.
  intros.
  unfold assign_ex in H. rewrite H. reflexivity.
Qed.
  

Definition assign_b (b a : bus) : bus :=
(* forall t : nat, (b t) = (a t). *)
  eval (econb b).



















