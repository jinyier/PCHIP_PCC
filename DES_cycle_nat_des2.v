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

Section des.
Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.


(* Definition bus := nat -> nat. (* the sensitivity tag is now a number stored
in sensitivity tag list. *) *)
Definition bus := nat.  (* The definition of bus is only a number indicating the position of the bus in the
sensitivity tag list. *)
Definition sense := nat.  (* Use 'sense' instead of 'nat' to represent the sensivitity. They are actually the 
same thing but of different names.  *)
Check bus.

(* Definition sen_list := nat -> list nat.*)
Definition sen_list := nat -> list sense.

Check sen_list.

Definition sliceA (b : bus) (p1 p2 : nat) : bus := b.

Definition sliceD (b : bus) (p1 p2 : nat) : bus := b.
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


Definition sen_update (sl : sen_list) (n : nat) (new_sen : nat) : sen_list :=
  fun t : nat => list_update (sl (t-1)) n new_sen.

Definition sen_update_null (sl : sen_list) : sen_list :=
  fun t : nat => sl (t-1).  (* only update time stamp. *)


Definition test := 1::3::5::3::11::6::nil.
Definition test4 := 2::2::6::2::12::5::nil.
Definition test2 := 2::6::16::nil.
Definition test3 : list nat := nil.

Definition test_sen := fun t : nat => test.
Definition test_sen2 := 
  fun t:nat => match t with
               | O => test
	       | S O => test2
	       | _ => test3
	       end.

Eval compute in sen_update test_sen2 2 666 6.
Eval compute in sen_update test_sen2 1 666.
Eval compute in list_update test 2 666.
Eval compute in list_update test3 666 3.

Eval compute in sen_update test_sen2 2 666 3.
Eval compute in sen_update (sen_update test_sen2 2 666) 1 33 0. 
Eval compute in sen_update (sen_update test_sen2 2 666) 1 33 1. 
Eval compute in sen_update (sen_update test_sen2 2 666) 1 33 2. 
Eval compute in sen_update (sen_update test_sen2 2 666) 1 33 3. 
Eval compute in sen_update (sen_update test_sen2 2 666) 1 33 4.

Definition test_sen3 := 
  fun t:nat => match t with
               | O => test4
               | _ => test3
               end.
Eval compute in sen_update (sen_update test_sen3 0 666) 0 666 2.
 
Eval compute in list_update test 666 4.
Eval compute in list_update test 666 5.
Eval compute in list_update test 666 6.
Eval compute in list_update test 666 7.
Eval compute in max_list test.


Definition lowertag (a : nat) : nat := pred a.

Definition a_number := 3.
Eval compute in lowertag a_number.

Eval compute in nth 1 (test_sen 0) 0.

(*
Definition bus_bit_not (b : bus) (sl : sen_list) (t : nat) : sense := 
  uoptag (nth b (sl t) 0).

Definition bus_bit_xor (a b : bus) (sl : sen_list) (t : nat) : sense :=
  boptag (nth a (sl t) 0) (nth b (sl t) 0).

Definition bus_bit_or (a b : bus) (sl : sen_list) (t : nat) : sense :=
  boptag (nth a (sl t) 0) (nth b (sl t) 0).

Definition bus_bit_and (a b : bus) (sl : sen_list) (t : nat) : sense :=
  boptag (nth a (sl t) 0) (nth b (sl t) 0).

Definition bus_app (a b : bus) (sl : sen_list) (t : nat) : sense :=
  boptag (nth a (sl t) 0) (nth b (sl t) 0).
*)

Fixpoint list_merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => nil
  | n1 :: l1' => match l2 with
                 | nil => nil
                 | n2 :: l2' => (boptag n1 n2) :: (list_merge l1' l2')
                 end
  end.

Definition sen_list_merge (sl1 sl2 : sen_list) : sen_list :=
  fun t : nat =>  list_merge (sl1 t) (sl2 t).

Check sen_list_merge test_sen2 test_sen3.
Eval compute in (sen_list_merge test_sen2 test_sen3) 0.
Eval compute in (sen_list_merge test_sen2 test_sen3) 1.
Eval compute in (sen_list_merge test_sen2 test_sen3) 2.
Eval compute in (sen_list_merge test_sen2 test_sen3) 3.
Eval compute in (sen_list_merge test_sen2 test_sen3) 4.

  
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

Fixpoint sen_eval (e : expr) (t : nat) (sl : sen_list) {struct e} : nat :=
  match e with
  | econv v => O
  | econb b => nth b (sl t) 0  (* The ending 0 is only used to indicate the nat property of nth function. *)
  | eand ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | eor ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | exor ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | enot ex => sen_eval ex t sl
  | eapp b1 b2 => boptag (nth b1 (sl t) 0) (nth b2 (sl t) 0)
  | cond cex ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | perm ex => lowertag (sen_eval ex t sl)
  | sbox b => nth b (sl t) 0
  | eq ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | lt ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | gt ex1 ex2 => boptag (sen_eval ex1 t sl) (sen_eval ex2 t sl)
  | case3 sel e1 e2 e3 e4 e5 e6 e7 e8 =>
		max_list 
                  ((sen_eval sel t sl) ::
                  (sen_eval e1 t sl) ::
                  (sen_eval e2 t sl) ::
                  (sen_eval e3 t sl) ::
                  (sen_eval e4 t sl) ::
                  (sen_eval e5 t sl) ::
                  (sen_eval e6 t sl) ::
                  (sen_eval e7 t sl) ::
                  (sen_eval e8 t sl) :: nil)
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




Fixpoint upd_signals_sen (c : code) (t : nat) (sl : sen_list) : sen_list :=
                 match c with
                 | assign_ex b ex => sen_update sl b (sen_eval ex (t-1) sl)
                 | assign_b b1 b2 => sen_update sl b1 (nth b2 (sl (t-1)) 0)
                 | assign_case3 b ex => sen_update sl b (sen_eval ex (t-1) sl)
                 | nonblock_assign_ex b ex => sen_update sl b (sen_eval ex (t-1) sl)  (* added in DES_frame_des.v. *)
                 | nonblock_assign_b b1 b2 => sen_update sl b1 (nth b2 (sl (t-1)) 0)    (* added in DES_frame_des.v. *)
                 | module_inst2in bout b1 b2 => sen_update_null sl     (* added in DES_frame_des.v to deal with module instantiation. *)
                 | module_inst3in bout b1 b2 b3 => sen_update_null sl  (* added in DES_frame_des.v to deal with module instantiation. *)
                 | codepile c1 c2 => sen_list_merge (upd_signals_sen c1 t sl) (upd_signals_sen c2 t sl)
                 end.


Definition upd_code_sen (n:nat)

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
Definition des_sen_list : sen_list := 
  fun t : nat => match t with
                 | O => 1::1::0::0::0::1::0::0::0::0::0::0::0::1::0::nil
(*                      |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  
                        0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
*)
                 | S _ => []
                 end.
(*
Definition des_sen_list : sen_list := fun t : nat => 1::1::0::0::0::1::0::0::0::0::0::0::0::0::0::nil.
                                                     |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  
                                                     0  1  2  3  4  5  6  7  8  9 10 11 12 13 14
*)
(*
Axiom secret_desIn : forall (t : nat), bus_sen desIn t = 1.         
Axiom secret_key : forall (t : nat), bus_sen key t = 1.             
Axiom secret_K_sub : forall (t : nat), bus_sen K_sub t = 1.

Axiom normal_decrypt : forall (t : nat), bus_sen decrypt t = 0.
Axiom normal_roundSel : forall (t : nat), bus_sen roundSel t = 0.
Axiom normal_clk : forall (t : nat), bus_sen clk t = 0.

Axiom normal_init_K_sub: bus_sen K_sub 0 = 0.  
Axiom normal_init_IP: bus_sen IP 0 = 0.        
Axiom normal_init_FP: bus_sen FP 0 = 0.        
Axiom normal_init_L: bus_sen L 0 = 0.          
Axiom normal_init_R: bus_sen R 0 = 0.          
Axiom normal_init_Xin: bus_sen Xin 0 = 0.      
Axiom normal_init_Lout: bus_sen Lout 0 = 0.    
Axiom normal_init_Rout: bus_sen Rout 0 = 0.    
Axiom normal_init_out: bus_sen out 0 = 0.      
Axiom normal_init_desOut: bus_sen desOut 0 = 0.
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



Eval compute in des_sen_list 0.
Eval compute in (upd_signals_sen des 1 des_sen_list) 0.
Eval compute in (upd_signals_sen des 1 des_sen_list) 1.
Eval compute in upd_signals_sen des 2 (upd_signals_sen des 1 des_sen_list) 3.
Eval compute in (upd_signals_sen des 1 des_sen_list) 2.

Theorem no_leaking : forall t : nat, t > 2 -> 








