
(* As the second step towards information flow secrecy tracking, I will try to 
dynamically trace the information flow tags for all internal/input/output signals.
Note that this work is based on my previous work (VTS 2012), a version that
the tracing of information flow tags is static. *)

(* Two examples will be used to demonstrate the effectiveness of the proposed 
method, DES and AES. The DES is the same as the one I used for VTS paper but no 
code modifications are added. The AES ...... *)

(* After finishing this work, my next step along this direction is to consider
feedback signals within processor-alike architectures. I've no idea how to solve
that problem for now but I'll try later. *)

(* Most of the Coq representatives for Verilog code are the same as for the VTS 
paper. *)

Eval compute in (pred 0).

Eval compute in lt 3 5.

Require Import Bool Arith List MinMax.

Search le.

Eval compute in max 3 5.



Inductive value := lo | hi.
Inductive sensitivity := protect | normal. 
(* I use 'protect' instead of 'secure' to make it clear the underlying signal
with 'protect' tag needs protection. *)

Section des.

Definition bus_value := list value.
(* Definition bus := nat -> (bus_value * sensitivity). *)
Definition bus := nat -> (bus_value * nat). (* the sensitivity tag is now a number indicating sensitivity level. *)


Definition VDD : bus := fun t : nat => (hi::nil, O).
Definition GND : bus := fun t : nat => (lo::nil, O).

Definition sliceA (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => (firstn (p2-p1+1) (skipn (p1-1) (fst (b t))), snd (b t)).

Definition v := lo::lo::hi::hi::lo::nil.

Definition b := fun t:nat => (v, 2).
Definition b2 := fun t:nat => (v, O).

Eval compute in sliceA b2 1 3.



Definition sliceD (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => match (b t) with
                 | (bv, n) => (rev (firstn (p1-p2+1) (skipn p2 (rev bv))), n)
                 end.

Notation "b [ m , n ] " := (sliceD b m n) (at level 50, left associativity).
Notation "b @ [ m , n ] " := (sliceA b m n) (at level 50, left associativity).

Eval compute in b[3,1].


Definition bus_length (b : bus) :=
  fun t : nat => length (fst (b t)).



Definition not (a : value) : value :=
  match a with 
  | lo => hi
  | hi => lo
  end.


(* BUS/TAG OPERATIONS. Ubiquitous calculation. *)
Fixpoint bv_bit_not (a : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => (not la) :: (bv_bit_not a')
  end.

Definition bus_bit_not (b : bus) : bus :=
  fun t : nat => (bv_bit_not (fst (b t)), snd (b t)).

Definition uoptag (a : nat) : nat := a.
Definition boptag (a b : nat) : nat := max a b.

Definition lowertag (a : nat) : nat := pred a.

Definition a_number := 3.
Eval compute in lowertag a_number.

Definition xor (a b : value) := 
  match a with
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
  end.   (* Again, only consider the case that bus widths are the same. *)

Definition bus_bit_xor (a b : bus) : bus :=
  fun t:nat => (bv_bit_xor (fst (a t)) (fst (b t)), boptag (snd (a t)) (snd (b t))).

Definition and (a b : value) : value :=
  match a with
  | lo => lo
  | hi => match b with
          | lo => lo
          | hi => hi
          end
  end.

Fixpoint bv_bit_and (a b : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (and la lb) :: (bv_bit_and a' b')
                end
  end.

Definition bus_bit_and (a b : bus) : bus :=
  fun t:nat => (bv_bit_and (fst (a t)) (fst (b t)), boptag (snd (a t)) (snd (b t))).

Eval compute in bus_bit_and b2 b2.

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

Definition bus_app (a b : bus) : bus :=
  fun t:nat => ((fst (a t)) ++ (fst (b t)), boptag (snd (a t)) (snd (b t))).


(* Some Comparison Operations. *)
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

Definition sen_eq (a b : nat) : value :=
  match (beq_nat a b) with
  | true => hi
  | false => lo
  end.


Definition bus_eq (a b : bus) (t : nat) : value :=
  and (bv_eq (fst (a t)) (fst (b t))) (sen_eq (snd (a t)) (snd (b t))).


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
  bv_lt (fst (a t)) (fst (b t)).    
(* Again, we assume that the tag of comparison buses are the same. *)

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
  bv_gt (fst (a t)) (fst (b t)).  
(* Again, we assume that the tag of comparison buses are the same. *)

Fixpoint bv_eq_0 (a : bus_value) {struct a} : value :=
  match a with
  | hi :: lt => lo
  | lo :: lt => bv_eq_0 lt
  | nil => hi
  end.

Definition bus_eq_0 (a : bus) (t : nat) : value :=
  bv_eq_0 (fst (a t)).   
(* Again, the sensitivity of the bus does not matter. *)
(* The comparison with 0 is used for most if-else branches. *)

Lemma bv_eq_refl : forall (t : nat) (a : bus_value), (bv_eq a a) = hi.
Proof.
  intros. unfold bv_eq.
  induction a. trivial.
  rewrite IHa. destruct a. trivial. trivial.
Qed.

Lemma bus_eq_refl : forall (t : nat) (a : bus), (bus_eq a a t) = hi.
Proof.
  intros. unfold bus_eq. unfold sen_eq. SearchAbout beq_nat. rewrite <- beq_nat_refl.
  SearchAbout bv_eq. rewrite bv_eq_refl. simpl. trivial. trivial.
Qed.

Lemma bus_eq_assign : forall (t : nat) (a b : bus), a = b -> (bus_eq a b t) = hi.
Proof. 
  intros. rewrite H. apply bus_eq_refl.
Qed.

Definition l_test : list nat := 3::4::6::nil.
Eval compute in nth 0 l_test.
  
(* Finishing basic operation definition. Note that we modified the notation of the sensitivity
tag from binary (secure|normal) to a multi-level natural number.
With the new sensitivity tag, we can represent more sophisticated circuit architecture with 
pipelines. *)

Inductive expr :=
  | econv : bus_value -> expr
  | econb : bus -> expr
  | eand : expr -> expr -> expr
  | eor : expr -> expr -> expr
  | exor : expr -> expr -> expr
  | cond : expr -> expr -> expr -> expr
  | perm : expr -> expr (* the permutation operation *)
  | sbox : bus -> expr (* sbox look-up *)
  | eq : expr -> expr -> expr
  | lt : expr -> expr -> expr
  | gt : expr -> expr -> expr
  | case3 : expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr.

Fixpoint eval (e : expr) (t : nat) {struct e} : bus_value*nat :=
  match e with
  | econv v => (v, O)
  | econb b => b t
  | eand ex1 ex2 => (bv_bit_and (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | eor ex1 ex2 => (bv_bit_or (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | exor ex1 ex2 => (bv_bit_xor (fst (eval ex1 t)) (fst (eval ex2 t)), boptag (snd (eval ex1 t)) (snd (eval ex2 t)))
  | enot ex => (bv_bit_not (fst (eval ex t)), uoptag (snd (eval ex t)))
  | cond cex ex1 ex2 => match (bv_eq_0 (fst (eval cex t))) with
                        | hi => eval ex1 t
                        | lo => eval ex2 t end
  | perm ex => (fst (eval ex t), lowertag (snd (eval ex t)))
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

Fixpoint eval_sen (e : expr) (t : nat) {struct e} : nat :=  (* only evalute the sensitivity tag. *)
  match e with
  | econv v => O
  | econb b => snd (b t)
  | eand ex1 ex2 => boptag (snd (eval ex1 t)) (snd (eval ex2 t))
  | eor ex1 ex2 => boptag (snd (eval ex1 t)) (snd (eval ex2 t))
  | exor ex1 ex2 => boptag (snd (eval ex1 t)) (snd (eval ex2 t))
  | enot ex => uoptag (snd (eval ex t))
  | cond cex ex1 ex2 => match (bv_eq_0 (fst (eval cex t))) with
                        | hi => eval_sen ex1 t
                        | lo => eval_sen ex2 t end
  | perm ex => lowertag (snd (eval ex t))
  | sbox b => snd (b t)
  | eq ex1 ex2 => match (bv_eq (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => O
                  | lo => O end
  | lt ex1 ex2 => match (bv_lt (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => O
                  | lo => O end
  | gt ex1 ex2 => match (bv_gt (fst (eval ex1 t)) (fst (eval ex2 t))) with
                  | hi => O
                  | lo => O end
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>     
                  match fst (eval sel t) with
                  | lo::lo::lo::nil => eval_sen e1 t
                  | lo::lo::hi::nil => eval_sen e2 t
                  | lo::hi::lo::nil => eval_sen e3 t
                  | lo::hi::hi::nil => eval_sen e4 t
                  | hi::lo::lo::nil => eval_sen e5 t
                  | hi::lo::hi::nil => eval_sen e6 t
                  | hi::hi::lo::nil => eval_sen e7 t
                  | hi::hi::hi::nil => eval_sen e8 t
                  | _ => eval_sen e1 t
                  end
  end.

Definition expr_sen (e : expr) (t : nat) : nat :=
  snd (eval e t).

Definition bus_sen (b : bus) (t : nat) : nat :=
  snd (eval (econb b) t).

Axiom sub_bus_sen : forall (t : nat) (p1 p2 : nat) (b : bus), 
  snd (b t) = snd ((b @ [p1, p2]) t).
(* ensure that any part of the bus shares the same sensitivity of the 
whole bus. *)


Inductive code := 
  | outb : bus -> code
  | inb : bus -> code
  | wireb : bus -> code
  | regb : bus -> code
  | assign_ex : bus -> expr -> code
  | assign_b : bus -> bus -> code
  (*| perm_b : bus -> code*)
  | assign_case3 : bus -> expr -> code
  | nonblock_assign_ex : bus -> expr -> code    (* added in DES_frame_des.v. *)
  | nonblock_assign_b : bus -> bus -> code   (* added in DES_frame_des.v. *)
  | module_inst2in : bus ->bus -> bus -> code    (* added in DES_frame_des.v to deal with module instantiation. *)
  | module_inst3in : bus -> bus -> bus -> bus -> code  (* added in DES_frame_des.v to deal with module instantiation. *)
  | codepile : code -> code -> code.

Notation " c1 ; c2 " := (codepile c1 c2) (at level 50, left associativity).

(* Let's only consider the case that each module only contains one output bus.
It holds for all modules in DES example. 
Or more precisely, return the sensitivity of the specific bus (manually iterate. *)
Fixpoint upd_code_sen (c : code) (t : nat) : 

Fixpoint chk_code_sen (c : code) (t : nat) : sensitivity :=
  match c with
  | outb b => normal
  | inb b => normal
  | wireb b => normal
  | regb b => normal
  | assign_ex b ex => expr_sen ex t
  | assign_b b1 b2 => bus_sen b2 t
  | assign_case3 b ex => expr_sen ex t
  | nonblock_assign_ex b ex => expr_sen ex t  (* added in DES_frame_des.v. *)
  | nonblock_assign_b b1 b2 => bus_sen b2 t  (* added in DES_frame_des.v. *)
  | module_inst2in bout b1 b2 => normal    (* added in DES_frame_des.v to deal with module instantiation. *)
  | module_inst3in bout b1 b2 b3 => normal  (* added in DES_frame_des.v to deal with module instantiation. *)
  | codepile c1 c2 => boptag (chk_code_sen c1 t) (chk_code_sen c2 t)
  end.















