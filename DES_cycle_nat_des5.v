(* As for the HOST paper, I'll use the DES_cycle_nat_des5.v as the starting point not to include the time stamp 
in the calculation for the purpose of simplified proof of final theorems. *)


(* Here is the non-time-stamp version of DES_cycle_nat_des3.v. *)
(* No time stamp is included in the definition of bus sensitivity. *)

(* Discussion notes with Zhong on Jan 7th 2012: 
1. Soundness, means correctness. That is, when the theorem is proved in Coq, it should be correct in any 
other environment. It's more related to Coq itself but not the way how I define statemen in the Coq.
2. Completeness. More strong than soundness.
3. To perform the same operation multiple times, one solution is to define a function with n (multiple times)
and operation function (or not).
4. Coq is quite aggressive in prove calculation results. That is, Coq will calculate the results first
(different to other less aggressive languages which require the proof of the calculation process). As a 
result, the theorem proof only requires a "reflexivity" static.
*)

(* Depart from the 'DES_cycle_nat_des.v' about the definition of time in signals and sensitivity list,
we now try to include time stamp in the bus definition. *)

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



Require Import Bool Arith List MinMax.
Require Omega.

Section des.
Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.


Definition bus := nat.  (* The definition of bus is only a number indicating the position of the bus in the
sensitivity tag list. *)
Definition sense := nat.  (* Use 'sense' instead of 'nat' to represent the sensivitity. They are actually the 
same thing but of different names.  *)

Definition bus_expr_sen := sense. 
Definition code_sen := list sense.

Definition sliceA (b : bus) (p1 p2 : nat) : bus := b.

Definition sliceD (b : bus) (p1 p2 : nat) : bus := b.
(* The slicing operation only keeps the bus sensitivity list position. 
It's reasonable and necessary to assume that any part of the bus shares the same sensitivity level
as the whole bus. And any changes to the part of the bus will be reflected on the whole bus 
sensitivity. *)

Notation "b [ m , n ] " := (sliceD b m n) (at level 50, left associativity).
Notation "b @ [ m , n ] " := (sliceA b m n) (at level 50, left associativity).


(* Now the return value of bus operation is a sense value, irrelevant to the origianl buses. *)

Definition uoptag (a : nat) : nat := a.
Definition boptag (a b : nat) : nat := max a b.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | nil => O
  | a :: rl => max a (max_list rl)
  end.

Definition list_update (sl : list nat) (pos : nat) (a : nat) : list nat :=
  (firstn pos sl) ++ (a::nil) ++ (skipn (pos+1) sl).


Definition code_sen_update (sl : code_sen) (n : nat) (new_sen : nat) : code_sen :=
  list_update sl n new_sen.

Definition code_sen_update_null (sl : code_sen) : code_sen :=
  sl.  (* only update time stamp. *)


Definition lowertag (a : nat) : nat := pred a.


Fixpoint list_merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => nil
  | n1 :: l1' => match l2 with
                 | nil => nil
                 | n2 :: l2' => (boptag n1 n2) :: (list_merge l1' l2')
                 end
  end.

Definition code_sen_merge (sl1 sl2 : code_sen) : code_sen :=
  list_merge sl1 sl2.

  
(* The expression is the smallest element of the Coq circuit representative.
The evaluation operation defines/calculate one signal nat value, the senstivitity tag, of the
whole expression. 
The later assignment statements will put the nat value back to the sensitivity list. *)  
Inductive expr :=
  | econv : nat -> expr
  | econb : bus -> expr
  | eand : expr -> expr -> expr
  | eor : expr -> expr -> expr
  | exor : expr -> expr -> expr
  | enot : expr -> expr
  | eapp : bus -> bus -> expr
  | cond : expr -> expr -> expr -> expr
  | perm : expr -> expr (* the permutation operation *)
  | sbox : bus -> expr (* sbox look-up *)
  | eq : expr -> expr -> expr
  | lt : expr -> expr -> expr
  | gt : expr -> expr -> expr
  | case3 : expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr -> expr.

Fixpoint expr_sen_eval (e : expr) (sl : code_sen) {struct e} : bus_expr_sen :=
  match e with
  | econv v => O
  | econb b => nth b sl 0  (* The ending 0 is only used to indicate the nat property of nth function. *)
  | eand ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | eor ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | exor ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | enot ex => expr_sen_eval ex sl
  | eapp b1 b2 => boptag (nth b1 (sl) 0) (nth b2 (sl) 0)
  | cond cex ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | perm ex => lowertag (expr_sen_eval ex sl)
  | sbox b => nth b (sl) 0
  | eq ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | lt ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | gt ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>
		max_list 
                  ((expr_sen_eval sel sl) ::
                  (expr_sen_eval e1 sl) ::
                  (expr_sen_eval e2 sl) ::
                  (expr_sen_eval e3 sl) ::
                  (expr_sen_eval e4 sl) ::
                  (expr_sen_eval e5 sl) ::
                  (expr_sen_eval e6 sl) ::
                  (expr_sen_eval e7 sl) ::
                  (expr_sen_eval e8 sl) :: nil)
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
  | assign_case3 : bus -> expr -> code
  | nonblock_assign_ex : bus -> expr -> code    (* added in DES_frame_des.v. *)
  | nonblock_assign_b : bus -> bus -> code   (* added in DES_frame_des.v. *)
  | module_inst2in : bus ->bus -> bus -> code    (* added in DES_frame_des.v to deal with module instantiation. *)
  | module_inst3in : bus -> bus -> bus -> bus -> code  (* added in DES_frame_des.v to deal with module instantiation. *)
  | codepile : code -> code -> code.

Notation " c1 ; c2 " := (codepile c1 c2) (at level 50, left associativity).




Fixpoint upd_code_sen (c : code) (sl : code_sen) : code_sen :=
                 match c with
                 | assign_ex b ex => code_sen_update sl b (expr_sen_eval ex sl)
                 | assign_b b1 b2 => code_sen_update sl b1 (nth b2 sl 0)
                 | assign_case3 b ex => code_sen_update sl b (expr_sen_eval ex sl)
                 | nonblock_assign_ex b ex => code_sen_update sl b (expr_sen_eval ex sl)  (* added in DES_frame_des.v. *)
                 | nonblock_assign_b b1 b2 => code_sen_update sl b1 (nth b2 sl 0)    (* added in DES_frame_des.v. *)
                 | module_inst2in bout b1 b2 => code_sen_update_null sl    (* added in DES_frame_des.v to deal with module instantiation. *)
                 | module_inst3in bout b1 b2 b3 => code_sen_update_null sl (* added in DES_frame_des.v to deal with module instantiation. *)
                 | codepile c1 c2 => code_sen_merge (upd_code_sen c1 sl) (upd_code_sen c2 sl)
                 end.


Fixpoint chk_code_sen (n:nat) (c:code) (sl : code_sen) : code_sen :=
  match n with
  | O => sl
  | S n' => chk_code_sen n' c (upd_code_sen c sl)
  end.


(* a.k.a. RTL code file *)
Definition desIn : bus      := 0.     (* #0 *)
Definition key : bus        := 1.     (* #1 *)
Definition decrypt : bus    := 2.     (* #2 *)
Definition roundSel : bus   := 3.     (* #3 *)
Definition clk : bus        := 4.     (* #4 *)

Definition K_sub : bus      := 5.     (* #5 *)
Definition IP : bus         := 6.     (* #6 *)
Definition FP : bus         := 7.     (* #7 *)
Definition L : bus          := 8.     (* #8 *)
Definition R : bus          := 9.     (* #9 *)
Definition Xin : bus        := 10.    (* #10 *)
Definition Lout : bus       := 11.    (* #11 *)
Definition Rout : bus       := 12.    (* #12 *)
Definition out : bus        := 13.    (* #13 *)

Definition desOut : bus     := 14.    (* #14 *)


(* the whole list for all input/output/internal signals *)
Definition des_code_sen : code_sen :=
    1::1::0::0::0::1::0::0::0::0::0::0::0::0::0::nil.
(*  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  
    0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
*)
    
Definition des_signals : signal :=
  outb desOut &   	(* #14 *)
  inb desIn &	        (* #0 *)
  inb key &             (* #1 *) 
  inb decrypt &         (* #2 *)
  inb roundSel &        (* #3 *)
  inb clk &             (* #4 *)
  wireb K_sub &		(* #5 *)
  wireb IP &		(* #6 *)
  wireb FP &		(* #7 *)
  regb L &		(* #8 *)
  regb R &		(* #9 *)
  wireb Xin &		(* #10 *)
  wireb Lout &		(* #11 *)
  wireb Rout &		(* #12 *)
  wireb out.		(* #13 *)


Definition des : code :=
  assign_ex Lout (cond (eq (econb roundSel) (econv (0))) (econb (IP @ [33, 64])) (econb R));
  assign_ex Xin (cond (eq (econb roundSel) (econv (0))) (econb (IP @ [1, 32])) (econb L));

  assign_ex Rout (exor (econb Xin) (econb out));
  assign_ex FP (eapp Rout Lout);
  
  module_inst2in out Lout K_sub;

  nonblock_assign_ex L (econb Lout);
  nonblock_assign_ex R (econb Rout);

  module_inst3in K_sub key roundSel decrypt;

  assign_ex IP (perm (econb desIn));
  assign_ex desOut (perm (econb FP)) 
(*  assign_ex desOut (cond (eq (econb roundSel) (econv 0)) (econb FP) (econb key))*)

.

(*

Eval compute in des_code_sen 0.
Eval compute in chk_code_sen 0 des des_code_sen.
Eval compute in chk_code_sen_detail 0 des des_code_sen.
Eval compute in chk_code_sen 1 des des_code_sen.
Eval compute in chk_code_sen_detail 1 des des_code_sen 0.
Eval compute in chk_code_sen_detail 1 des des_code_sen 1.
Eval compute in chk_code_sen_detail 1 des des_code_sen 2.
Eval compute in chk_code_sen 2 des des_code_sen.
Eval compute in chk_code_sen_detail 2 des des_code_sen 0.
Eval compute in chk_code_sen_detail 2 des des_code_sen 1.
Eval compute in chk_code_sen_detail 2 des des_code_sen 2.
Eval compute in chk_code_sen_detail 2 des des_code_sen 3.
Eval compute in chk_code_sen 3 des des_code_sen.
*)

Lemma stable_code_sen :  upd_code_sen des des_code_sen = des_code_sen.
Proof.
  intros. reflexivity.
Qed.



Theorem no_leaking : forall t : nat, t > 2 -> 
  (chk_code_sen t des des_code_sen) = 1::1::0::0::0::1::0::0::0::0::0::0::0::0::0::nil.
Proof. 
  intros. induction H. reflexivity.
  unfold chk_code_sen. rewrite stable_code_sen. simpl. apply IHle.
Qed.







