(* In order to support fully sensitivity tag assignments, I revamp the whole Coq circuit 
representative architecture with the first step is redefine the bus architecture:
*** Definition bus := nat -> nat.
With the first nat denoting time, the second nat denoting the position of the bus in the 
whole sensitivity tag list.
    We also add a new sensitivity tag list to represent all internal signals' sensitivities 
associated with time.
*** Definition sen_list := nat -> list nat.
*)


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





Section des.

Definition bus := nat -> nat. (* the sensitivity tag is now a number stored
in sensitivity tag list. *)

Definition sen_list := nat -> list nat.

Definition sliceA (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => (b t).

Definition sliceD (b : bus) (p1 p2 : nat) : bus :=
  fun t : nat => (b t).
(* The slicing operation only keeps the bus sensitivity list position. 
It's reasonable and necessary to assume that any part of the bus shares the same sensitivity level
as the whole bus. And any changes to the part of the bus will be reflected on the whole bus 
sensitivity. *)

Notation "b [ m , n ] " := (sliceD b m n) (at level 50, left associativity).
Notation "b @ [ m , n ] " := (sliceA b m n) (at level 50, left associativity).

(* No bus length operation is required in this new model.
Definition bus_length (b : bus) :=
  fun t : nat => length (fst (b t)).
*)


Definition bus_bit_not (b : bus) : bus :=
  fun t : nat => (b t).

Definition uoptag (a : nat) : nat := a.
Definition boptag (a b : nat) : nat := max a b.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => O
  | a :: rl => max a (max_list rl)
  end.

Definition list_update (sl : list nat) (pos : nat) (a : nat) : list nat :=
  (firstn pos sl) ++ (a::nil) ++ (skipn (pos+1) sl).

  Fixpoint firstn (n:nat)(l:sen_list) : sen_list :=
    match n with
      | 0 => nil
      | S n => match l with
                 | nil => nil
                 | a::l => a::(firstn n l)
               end
    end.

  Fixpoint skipn (n:nat)(l:list A) : list A :=
    match n with
      | 0 => l
      | S n => match l with
                 | nil => nil
                 | a::l => skipn n l
               end
    end.

Definition sen_update (sl : sen_list) (n : nat) (new_sen : nat) : sen_list :=
  (firstn n sl) ++ (new_sen::nil) ++ (skipn (n+1) sl).
soif
Definition test := 1::3::5::3::11::6::nil.
Eval compute in sen_update test 0 666.
Eval compute in sen_update test 1 666.
Eval compute in list_update test 2 666.
Eval compute in list_update test 666 3.
Eval compute in list_update test 666 4.
Eval compute in list_update test 666 5.
Eval compute in list_update test 666 6.
Eval compute in list_update test 666 7.
Eval compute in max_list test.


Definition lowertag (a : nat) : nat := pred a.

Definition a_number := 3.
Eval compute in lowertag a_number.

Definition bus_bit_xor (a b : bus) : bus :=
  fun t:nat => boptag (a t) (b t).

Definition bus_bit_and (a b : bus) : bus :=
  fun t:nat => boptag (a t) (b t)(b t).

Definition bus_bit_or (a b : bus) : bus :=
  fun t:nat => boptag (a t) (b t).

Definition bus_app (a b : bus) : bus :=
  fun t:nat => boptag (a t) (b t).


(* No operations are required in the new model. *)

Definition sen_eq (a b : nat) : value := beq_nat a b.

Definition bus_eq (a b : bus) (t : nat) : bus :=
  fun t:nat => boptag (a t) (b t).

Definition bus_lt (a b : bus) (t : nat) : bus :=
  fun t:nat => boptag (a t) (b t).

Definition bus_gt (a b : bus) (t : nat) : bus :=
  fun t:nat => boptag (a t) (b t).

Definition bus_eq_0 (a : bus) (t : nat) : bus := a.

(*
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
*)

Fixpoint sen_list_merge (sl1 sl2 : list nat) : list nat :=
  match sl1 with
  | nil => nil
  | n1 :: sl1' => match sl2 with
	          | nil => nil
		  | n2 :: sl2' => (boptag n1 n2) :: (sen_list_merge sl1' sl2')
		  end
  end.
  
(* The expression is the smallest element of the Coq circuit representative.
The evaluation operation defines/calculate one signal nat value, the senstivitity tag, of the
whole expression. 
The later assignment statements will put the nat value back to the sensitivity list. *)  
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

Fixpoint sen_eval (e : expr) (t : nat) (sl : sen_list){struct e} : nat :=
  match e with
  | econv v => O
  | econb b => nth (b t) (sl t)
  | eand ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | eor ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | exor ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | enot ex => sen_eval ex t sl
  | cond cex ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | perm ex => lowertag (sen_eval ex t sl)
  | sbox b => nth (b t) (sl t)
  | eq ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | lt ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | gt ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>
		max_list 
                  (sen_eval sel t sl) ::
                  (sen_eval e1 t sl) ::
                  (sen_eval e2 t sl) ::
                  (sen_eval e3 t sl) ::
                  (sen_eval e4 t sl) ::
                  (sen_eval e5 t sl) ::
                  (sen_eval e6 t sl) ::
                  (sen_eval e7 t sl) ::
                  (sen_eval e8 t sl) :: nil
  end.


Inductive signal :=
  | outb : bus -> signal
  | inb : bus -> signal
  | wireb : bus -> signal
  | regb : bus -> signal
  | signalpile : signal -> signal -> signal.

Notation " s1 & s2 " := (signalpile s1 s2) (at level 50, left associativity).

Inductive code :=
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


(* a.k.a. RTL code file *)

Variables desOut : bus.
Variables desIn key : bus.
Variables decrypt roundSel clk : bus.
Variables K_sub IP FP L R Xin Lout Rout out : bus.

Variable des_sen_list : sen_list.

Axiom secret_key : forall (t : nat), bus_sen key t = 1.
Axiom secret_desIn : forall (t : nat), bus_sen desIn t = 1.
Axiom secret_K_sub : forall (t : nat), bus_sen K_sub t = 1.

Axiom normal_init_K_sub: bus_sen K_sub 0 = 0.  (* #0 *)
Axiom normal_init_IP: bus_sen IP 0 = 0.        (* #1 *)
Axiom normal_init_FP: bus_sen FP 0 = 0.        (* #2 *)
Axiom normal_init_L: bus_sen L 0 = 0.          (* #3 *)
Axiom normal_init_R: bus_sen R 0 = 0.          (* #4 *)
Axiom normal_init_Xin: bus_sen Xin 0 = 0.      (* #5 *)
Axiom normal_init_Lout: bus_sen Lout 0 = 0.    (* #6 *)
Axiom normal_init_Rout: bus_sen Rout 0 = 0.    (* #7 *)
Axiom normal_init_out: bus_sen out 0 = 0.      (* #8 *)
Axiom normal_init_desOut: bus_sen desOut 0 = 0.(* #9 *)

Definition des_signals : signal :=
  outb desOut &   	(* #9 *)
  inb desIn &	
  inb key &
  inb decrypt &
  inb roundSel &
  inb clk &
  wireb K_sub &		(* #0 *)
  wireb IP &		(* #1 *)
  wireb FP &		(* #2 *)
  regb L &		(* #3 *)
  regb R &		(* #4 *)
  wireb Xin &		(* #5 *)
  wireb Lout &		(* #6 *)
  wireb Rout &		(* #7 *)
  wireb out.		(* #8 *)


Fixpoint upd_signals_sen (c : code) (t : nat) (sl : sen_list) : sen_list :=
  match c with
  | assign_ex b ex => sen_update sl (b t) (sen_eval ex t sl)
  | assign_b b1 b2 => bus_sen b2 t
  | assign_case3 b ex => expr_sen ex t
  | nonblock_assign_ex b ex => expr_sen ex t  (* added in DES_frame_des.v. *)
  | nonblock_assign_b b1 b2 => bus_sen b2 t  (* added in DES_frame_des.v. *)
  | module_inst2in bout b1 b2 => normal    (* added in DES_frame_des.v to deal with module instantiation. *)
  | module_inst3in bout b1 b2 b3 => normal  (* added in DES_frame_des.v to deal with module instantiation. *)
  | codepile c1 c2 => boptag (chk_code_sen c1 t) (chk_code_sen c2 t)



  | codepile c1 c2 => sen_list_merge (upd_signals_sen c1) (upd_signals_sen c2)
  | 


Definition line1 : code :=
  assign_ex Lout (cond (eq (econb roundSel) (econv (lo::lo::lo::lo::nil))) (econb (IP @ [33, 64])) (econb R)).
(* Lout => #6 *)
Definition upd_sen_line1 (sl : list nat) : list nat :=
  

Definition line2 : code :=
  assign_ex Xin (cond (eq (econb roundSel) (econv (lo::lo::lo::lo::nil))) (econb (IP @ [1, 32])) (econb L)).
(* Xin => #5 *)

Definition line3 : code :=
  assign_ex Rout (econb (bus_bit_xor Xin out)).
(* Rout => #7 *)

Definition line4 : code :=
  assign_ex FP (econb (bus_app Rout Lout)).
(* FP => #2 *)

Definition line5 : code :=
  module_inst2in out Lout K_sub.
(* out => #8 *)

Definition line6 : code :=
  nonblock_assign_ex L (econb Lout).
(* L => #3 *)

Definition line7 : code :=
  nonblock_assign_ex R (econb Rout).
(* R => #4 *)

Definition line8 : code :=
  module_inst3in K_sub key roundSel decrypt.
(* K_sub => #0 *)

Definition line9 : code :=
  assign_ex IP (perm (econb desIn)).
(* IP => #1 *)

Definition line10 : code :=
  assign_ex desOut (perm (econb FP)).
(* desOut => #9 *)







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















