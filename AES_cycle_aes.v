(* This is the first try on AES encryption core with the denotation derived from "DES_cycle_nat_des5.v".
The Verilog code is, again, the Rudolf version downloaded from Opencores. Similar to the example of DES core 
I used for VTS 2012, it is not a good sample for a pipleline design. It is, in reality, a one stage (area optimized)
AES encryption core with a internal loop control (a downward counter). 
So similar methods tracking information flow developed in DES core should apply here in AES.

And, hopefully, this method can be expanded to deep pipelined designs and processor level feedback designs. 1/10/2012
*)


Require Import Bool Arith List MinMax.
Require Omega.
Set Printing Depth 1000.
Set Printing Width 1000.

Section aes.
(* Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope. *)


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

Definition code_sen_update_m4 (sl : code_sen) (n1 n2 n3 n4 : nat) (new_sen : nat) : code_sen :=
  list_update (list_update (list_update (list_update sl n1 new_sen) n2 new_sen) n3 new_sen) n4 new_sen.

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
  | eand_bit : bus -> expr      (* bit wise operation on buses /AES/*)
  | eor_bit : bus -> expr	(* /AES/*)
  | exor_bit : bus -> expr	(* /AES/*)
  | eplus : expr -> expr -> expr 	(* PLUS operation between buses and constant /AES/*)
  | eminus : expr -> expr -> expr	(* MINUS operation /AES/*)
  | enot : expr -> expr
  | eapp : bus -> bus -> expr
  | cond : expr -> expr -> expr -> expr
  | perm : expr -> expr (* the permutation operation *)
  | exor_key : bus -> bus -> expr (* the operaton of XOR a bus with the key *)
  | sbox : bus -> expr (* sbox look-up, both for /DES/ and /AES/*)
  | mix_col : bus -> bus -> bus -> bus -> expr  (* Mix column operation /AES/ *)
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
  | eand_bit b => nth b sl 0 (* bit wise operation on buses do not change the sensivity of the bus /AES/*)
  | eor_bit b => nth b sl 0  (* /AES/ *)
  | exor_bit b => nth b sl 0 (* /AES/ *)
  | eplus ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)  (* /AES/ *)
  | eminus ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl) (* /AES/ *)
  | enot ex => expr_sen_eval ex sl
  | eapp b1 b2 => boptag (nth b1 (sl) 0) (nth b2 (sl) 0)
  | cond cex ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | perm ex => lowertag (expr_sen_eval ex sl)
  | exor_key b key => lowertag (boptag (nth b sl 0) (nth key sl 0))  (* The only operation in AES to decrease sensitivity level except sub-module. *)
  | sbox b => nth b (sl) 0
  | mix_col b1 b2 b3 b4 => max_list ((nth b1 sl 0)::(nth b2 sl 0)::(nth b3 sl 0)::(nth b4 sl 0)::nil)  (* can also use eapp operation *)
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
  | assign_mix_col : bus -> bus -> bus -> bus -> expr -> code  (* to deal with the 4 bytes mix column operation *)
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
                 | assign_mix_col b1 b2 b3 b4 ex => code_sen_update_m4 sl b1 b2 b3 b4 (expr_sen_eval ex sl)  (* update all four signals at once *)
                 | nonblock_assign_ex b ex => code_sen_update sl b (expr_sen_eval ex sl)  (* added in DES_frame_des.v. *)
                 | nonblock_assign_b b1 b2 => code_sen_update sl b1 (nth b2 sl 0)    (* added in DES_frame_des.v. *)
                 | module_inst2in bout b1 b2 => code_sen_update_null sl    (* added in DES_frame_des.v to deal with module instantiation. *)
                 | module_inst3in bout b1 b2 b3 => code_sen_update_null sl (* added in DES_frame_des.v to deal with module instantiation. *)
                 | codepile c1 c2 => code_sen_merge (upd_code_sen c1 sl) (upd_code_sen c2 sl)
                 end.


(* Fixpoint chk_code_sen (n:nat) (c:code) (sl : code_sen) : code_sen := *)
(*   match n with *)
(*   | O => sl *)
(*   | S n' => chk_code_sen n' c (upd_code_sen c sl) *)
(*   end. *)

Fixpoint chk_code_sen (t:nat) (c:code) (sl : code_sen) : code_sen :=
  match t with
  | O => sl
  | S t' => upd_code_sen c (chk_code_sen t' c sl)
  end.

(********************************************************* *)
(* Derived from aes_signals. *)
(*inputs *)
Definition clk : bus		:= 0.
Definition rst : bus		:= 1.
Definition ld : bus		:= 2.
Definition key : bus		:= 3.   (* secure *)
Definition text_in : bus	:= 4.   (* secure *)

(* start internal signals *)
Definition w : bus		:= 5.
Definition w0 : bus		:= 6.
Definition w1 : bus		:= 7.
Definition w2 : bus		:= 8.
Definition w3 : bus		:= 9.
Definition text_in_r : bus	:= 10.

(* 16 bytes internal state *)
Definition sa00 : bus		:= 11.
Definition sa01 : bus		:= 12.
Definition sa02 : bus		:= 13.
Definition sa03 : bus		:= 14.
Definition sa10 : bus		:= 15.
Definition sa11 : bus		:= 16.
Definition sa12 : bus		:= 17.
Definition sa13 : bus		:= 18.
Definition sa20 : bus		:= 19.
Definition sa21 : bus		:= 20.
Definition sa22 : bus		:= 21.
Definition sa23 : bus		:= 22.
Definition sa30 : bus		:= 23.
Definition sa31 : bus		:= 24.
Definition sa32 : bus		:= 25.
Definition sa33 : bus		:= 26.

Definition sa00_next : bus	:= 27.
Definition sa01_next : bus	:= 28.
Definition sa02_next : bus	:= 29.
Definition sa03_next : bus	:= 30.
Definition sa10_next : bus	:= 31.
Definition sa11_next : bus	:= 32.
Definition sa12_next : bus	:= 33.
Definition sa13_next : bus	:= 34.
Definition sa20_next : bus	:= 35.
Definition sa21_next : bus	:= 36.
Definition sa22_next : bus	:= 37.
Definition sa23_next : bus	:= 38.
Definition sa30_next : bus	:= 39.
Definition sa31_next : bus	:= 40.
Definition sa32_next : bus	:= 41.
Definition sa33_next : bus	:= 42.

Definition sa00_sub : bus	:= 43.
Definition sa01_sub : bus	:= 44.
Definition sa02_sub : bus	:= 45.
Definition sa03_sub : bus	:= 46.
Definition sa10_sub : bus	:= 47.
Definition sa11_sub : bus	:= 48.
Definition sa12_sub : bus	:= 49.
Definition sa13_sub : bus	:= 50.
Definition sa20_sub : bus	:= 51.
Definition sa21_sub : bus	:= 52.
Definition sa22_sub : bus	:= 53.
Definition sa23_sub : bus	:= 54.
Definition sa30_sub : bus	:= 55.
Definition sa31_sub : bus	:= 56.
Definition sa32_sub : bus	:= 57.
Definition sa33_sub : bus	:= 58.

Definition sa00_sr : bus	:= 59.
Definition sa01_sr : bus	:= 60.
Definition sa02_sr : bus	:= 61.
Definition sa03_sr : bus	:= 62.
Definition sa10_sr : bus	:= 63.
Definition sa11_sr : bus	:= 64.
Definition sa12_sr : bus	:= 65.
Definition sa13_sr : bus	:= 66.
Definition sa20_sr : bus	:= 67.
Definition sa21_sr : bus	:= 68.
Definition sa22_sr : bus	:= 69.
Definition sa23_sr : bus	:= 70.
Definition sa30_sr : bus	:= 71.
Definition sa31_sr : bus	:= 72.
Definition sa32_sr : bus	:= 73.
Definition sa33_sr : bus	:= 74.

Definition sa00_mc : bus	:= 75.
Definition sa01_mc : bus	:= 76.
Definition sa02_mc : bus	:= 77.
Definition sa03_mc : bus	:= 78.
Definition sa10_mc : bus	:= 79.
Definition sa11_mc : bus	:= 80.
Definition sa12_mc : bus	:= 81.
Definition sa13_mc : bus	:= 82.
Definition sa20_mc : bus	:= 83.
Definition sa21_mc : bus	:= 84.
Definition sa22_mc : bus	:= 85.
Definition sa23_mc : bus	:= 86.
Definition sa30_mc : bus	:= 87.
Definition sa31_mc : bus	:= 88.
Definition sa32_mc : bus	:= 89.
Definition sa33_mc : bus	:= 90.


Definition ld_r : bus		:= 91.
Definition dcnt : bus		:= 92.
(* end internal signals *)

(* outputs *)
Definition text_out : bus	:= 93.
Definition done : bus		:= 94.



(* a.k.a. RTL code file *)
Definition aes_signals : signal :=
(* inputs *)
inb clk &
inb rst &
inb ld  &
inb key &   (* secure *)
inb text_in &   (* secure *)   

(* outputs *)
outb done &
outb text_out &

(* internal signals *)
wireb w  &
wireb w0 &
wireb w1 &
wireb w2 &
wireb w3 &
regb text_in_r &  
regb text_out  & 

(* 16 bytes internal state *)
regb sa00 &
regb sa01 &
regb sa02 &
regb sa03 &
regb sa10 &
regb sa11 &
regb sa12 &
regb sa13 &
regb sa20 &
regb sa21 &
regb sa22 &
regb sa23 &
regb sa30 &
regb sa31 &
regb sa32 &
regb sa33 &

wireb sa00_next &
wireb sa01_next &
wireb sa02_next &
wireb sa03_next &
wireb sa10_next &
wireb sa11_next &
wireb sa12_next &
wireb sa13_next &
wireb sa20_next &
wireb sa21_next &
wireb sa22_next &
wireb sa23_next &
wireb sa30_next &
wireb sa31_next &
wireb sa32_next &
wireb sa33_next &

wireb sa00_sub &
wireb sa01_sub &
wireb sa02_sub &
wireb sa03_sub &
wireb sa10_sub &
wireb sa11_sub &
wireb sa12_sub &
wireb sa13_sub &
wireb sa20_sub &
wireb sa21_sub &
wireb sa22_sub &
wireb sa23_sub &
wireb sa30_sub &
wireb sa31_sub &
wireb sa32_sub &
wireb sa33_sub &

wireb sa00_sr  &
wireb sa01_sr  &
wireb sa02_sr  &
wireb sa03_sr  &
wireb sa10_sr  &
wireb sa11_sr  &
wireb sa12_sr  &
wireb sa13_sr  &
wireb sa20_sr  &
wireb sa21_sr  &
wireb sa22_sr  &
wireb sa23_sr  &
wireb sa30_sr  &
wireb sa31_sr  &
wireb sa32_sr  &
wireb sa33_sr  &

wireb sa00_mc  &
wireb sa01_mc  &
wireb sa02_mc  &
wireb sa03_mc  &
wireb sa10_mc  &
wireb sa11_mc  &
wireb sa12_mc  &
wireb sa13_mc  &
wireb sa20_mc  &
wireb sa21_mc  &
wireb sa22_mc  &
wireb sa23_mc  &
wireb sa30_mc  &
wireb sa31_mc  &
wireb sa32_mc  &
wireb sa33_mc  &

regb ld_r &
regb dcnt.

(* the whole list for all input/output/internal signals *)
Definition aes_initial_list : code_sen :=
    0::0::0::1::2::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::
(*  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  
    0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44
*)
    0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::
(*  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  |  
   45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89
*)
    0::0::0::0::0::nil.
(*  |  |  |  |  |  
   90 91 92 93 94 
*)


(* ************************************************************** *)
(* AES code *)
Definition aes : code :=
  assign_b w3 (w [127 , 96]);
  assign_b w2 (w[ 95, 64]);
  assign_b w1 (w[ 63, 32]);
  assign_b w0 (w[ 31,  0]);

(* // Misc Logic *)
  nonblock_assign_ex dcnt (cond (enot (econb rst)) (econv 0)
                                                   (cond (econb ld) (econv 10)
                                                                   (cond (eor_bit dcnt) (eminus (econb dcnt) (econv 1)) (econb dcnt)
                                                                   )
                                                   )
                               
                           );
  nonblock_assign_ex done   (eand (eand (enot (eor_bit (dcnt[3,1]))) (econb (dcnt[0,0]))) (enot (econb ld)));
  nonblock_assign_ex text_in_r    (cond (econb ld) (econb text_in) (econb text_in_r));
  nonblock_assign_b ld_r ld;

(* // Initial Permutation (AddRoundKey) *)
  nonblock_assign_ex sa33   (cond (econb ld_r) (exor_key (text_in_r[  7,  0]) (w3[ 7, 0])) (econb sa33_next));
  nonblock_assign_ex sa23   (cond (econb ld_r) (exor_key (text_in_r[ 15,  8]) (w3[15, 8])) (econb sa23_next));
  nonblock_assign_ex sa13   (cond (econb ld_r) (exor_key (text_in_r[ 23, 16]) (w3[23,16])) (econb sa13_next));
  nonblock_assign_ex sa03   (cond (econb ld_r) (exor_key (text_in_r[ 31, 24]) (w3[31,24])) (econb sa03_next));
  nonblock_assign_ex sa32   (cond (econb ld_r) (exor_key (text_in_r[ 39, 32]) (w2[ 7, 0])) (econb sa32_next));
  nonblock_assign_ex sa22   (cond (econb ld_r) (exor_key (text_in_r[ 47, 40]) (w2[15, 8])) (econb sa22_next));
  nonblock_assign_ex sa12   (cond (econb ld_r) (exor_key (text_in_r[ 55, 48]) (w2[23,16])) (econb sa12_next));
  nonblock_assign_ex sa02   (cond (econb ld_r) (exor_key (text_in_r[ 63, 56]) (w2[31,24])) (econb sa02_next));
  nonblock_assign_ex sa31   (cond (econb ld_r) (exor_key (text_in_r[ 71, 64]) (w1[ 7, 0])) (econb sa31_next));
  nonblock_assign_ex sa21   (cond (econb ld_r) (exor_key (text_in_r[ 79, 72]) (w1[15, 8])) (econb sa21_next));
  nonblock_assign_ex sa11   (cond (econb ld_r) (exor_key (text_in_r[ 87, 80]) (w1[23,16])) (econb sa11_next));
  nonblock_assign_ex sa01   (cond (econb ld_r) (exor_key (text_in_r[ 95, 88]) (w1[31,24])) (econb sa01_next));
  nonblock_assign_ex sa30   (cond (econb ld_r) (exor_key (text_in_r[103, 96]) (w0[ 7, 0])) (econb sa30_next));
  nonblock_assign_ex sa20   (cond (econb ld_r) (exor_key (text_in_r[111,104]) (w0[15, 8])) (econb sa20_next));
  nonblock_assign_ex sa10   (cond (econb ld_r) (exor_key (text_in_r[119,112]) (w0[23,16])) (econb sa10_next));
  nonblock_assign_ex sa00   (cond (econb ld_r) (exor_key (text_in_r[127,120]) (w0[31,24])) (econb sa00_next));

(* // Round Permutations *)
  assign_b sa00_sr sa00_sub;
  assign_b sa01_sr sa01_sub;
  assign_b sa02_sr sa02_sub;
  assign_b sa03_sr sa03_sub;
  assign_b sa10_sr sa10_sub;
  assign_b sa11_sr sa11_sub;
  assign_b sa12_sr sa12_sub;
  assign_b sa13_sr sa13_sub;
  assign_b sa20_sr sa20_sub;
  assign_b sa21_sr sa21_sub;
  assign_b sa22_sr sa22_sub;
  assign_b sa23_sr sa23_sub;
  assign_b sa30_sr sa30_sub;
  assign_b sa31_sr sa31_sub;
  assign_b sa32_sr sa32_sub;
  assign_b sa33_sr sa33_sub;  

  assign_mix_col sa00_mc sa10_mc sa20_mc sa30_mc (mix_col sa00_sr sa10_sr sa20_sr sa30_sr);
  assign_mix_col sa01_mc sa11_mc sa21_mc sa31_mc (mix_col sa01_sr sa11_sr sa21_sr sa31_sr);
  assign_mix_col sa02_mc sa12_mc sa22_mc sa32_mc (mix_col sa03_sr sa12_sr sa22_sr sa32_sr);
  assign_mix_col sa03_mc sa13_mc sa23_mc sa33_mc (mix_col sa03_sr sa13_sr sa23_sr sa33_sr);

  assign_ex sa00_next  (exor_key sa00_mc (w0[31,24]));
  assign_ex sa01_next  (exor_key sa01_mc (w1[31,24]));
  assign_ex sa02_next  (exor_key sa02_mc (w2[31,24]));
  assign_ex sa03_next  (exor_key sa03_mc (w3[31,24]));
  assign_ex sa10_next  (exor_key sa10_mc (w0[23,16]));
  assign_ex sa11_next  (exor_key sa11_mc (w1[23,16]));
  assign_ex sa12_next  (exor_key sa12_mc (w2[23,16]));
  assign_ex sa13_next  (exor_key sa13_mc (w3[23,16]));
  assign_ex sa20_next  (exor_key sa20_mc (w0[15, 8]));
  assign_ex sa21_next  (exor_key sa21_mc (w1[15, 8]));
  assign_ex sa22_next  (exor_key sa22_mc (w2[15, 8]));
  assign_ex sa23_next  (exor_key sa23_mc (w3[15, 8]));
  assign_ex sa30_next  (exor_key sa30_mc (w0[ 7, 0]));
  assign_ex sa31_next  (exor_key sa31_mc (w1[ 7, 0]));
  assign_ex sa32_next  (exor_key sa32_mc (w2[ 7, 0]));
  assign_ex sa33_next  (exor_key sa33_mc (w3[ 7, 0]));
  
(* // Final text output *)
  nonblock_assign_ex (text_out[127,120])  (exor_key sa00_sr (w0[31,24]));
  nonblock_assign_ex (text_out[ 95, 88])  (exor_key sa01_sr (w1[31,24]));
  nonblock_assign_ex (text_out[ 63, 56])  (exor_key sa02_sr (w2[31,24]));
  nonblock_assign_ex (text_out[ 31, 24])  (exor_key sa03_sr (w3[31,24]));
  nonblock_assign_ex (text_out[119,112])  (exor_key sa10_sr (w0[23,16]));
  nonblock_assign_ex (text_out[ 87, 80])  (exor_key sa11_sr (w1[23,16]));
  nonblock_assign_ex (text_out[ 55, 48])  (exor_key sa12_sr (w2[23,16]));
  nonblock_assign_ex (text_out[ 23, 16])  (exor_key sa13_sr (w3[23,16]));
  nonblock_assign_ex (text_out[111,104])  (exor_key sa20_sr (w0[15, 8]));
  nonblock_assign_ex (text_out[ 79, 72])  (exor_key sa21_sr (w1[15, 8]));
  nonblock_assign_ex (text_out[ 47, 40])  (exor_key sa22_sr (w2[15, 8]));
  nonblock_assign_ex (text_out[ 15,  8])  (exor_key sa23_sr (w3[15, 8]));
  nonblock_assign_ex (text_out[103, 96])  (exor_key sa30_sr (w0[ 7, 0]));
  nonblock_assign_ex (text_out[ 71, 64])  (exor_key sa31_sr (w1[ 7, 0]));
  nonblock_assign_ex (text_out[ 39, 32])  (exor_key sa32_sr (w2[ 7, 0]));
  nonblock_assign_ex (text_out[  7,  0])  (exor_key sa33_sr (w3[ 7, 0]));

(* // Modules *)
  module_inst3in w clk ld key;

  assign_ex sa00_sub (sbox sa00);
  assign_ex sa01_sub (sbox sa01);
  assign_ex sa02_sub (sbox sa02);
  assign_ex sa03_sub (sbox sa03);
  assign_ex sa10_sub (sbox sa10);
  assign_ex sa11_sub (sbox sa11);
  assign_ex sa12_sub (sbox sa12);
  assign_ex sa13_sub (sbox sa13);
  assign_ex sa20_sub (sbox sa20);
  assign_ex sa21_sub (sbox sa21);
  assign_ex sa22_sub (sbox sa22);
  assign_ex sa23_sub (sbox sa23);
  assign_ex sa30_sub (sbox sa30);
  assign_ex sa31_sub (sbox sa31);
  assign_ex sa32_sub (sbox sa32);
  assign_ex sa33_sub (sbox sa33)
.

(* Stabalization testing procedure 
Print aes_sen_initial.
Eval vm_compute in aes_sen_initial.
Eval vm_compute in chk_code_sen 0 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 1 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 2 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 3 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 4 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 5 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 6 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 7 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 8 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 9 aes aes_sen_initial.
Eval vm_compute in chk_code_sen 15 aes aes_sen_initial.
*)

Definition aes_stable_list : code_sen :=
0 :: 0 :: 0 :: 1 :: 2 :: 0 :: 0 :: 0 :: 0 :: 0 :: 
2 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 0 :: 0 :: 0 :: 
0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 
0 :: 0 :: 0 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 
1 :: 0 :: 0 :: 0 :: 0 :: nil.

Lemma aes_sen_stable :  upd_code_sen aes aes_stable_list = aes_stable_list.
Proof.
  intros. vm_compute. reflexivity.
Qed.

Lemma stable_code_sen_chk : forall t:nat, chk_code_sen t aes aes_stable_list = aes_stable_list.
Proof.
  intros. 
  induction t. vm_compute. reflexivity.
  unfold chk_code_sen. fold chk_code_sen. 
  rewrite IHt.
  apply aes_sen_stable.
Qed.

Lemma stable_state : forall t:nat, t = 5 -> chk_code_sen t aes aes_initial_list = aes_stable_list.
Proof.
  intros.
  rewrite H. vm_compute. reflexivity.
Qed.

Theorem fp_list_accessability : forall t : nat, t > 5 -> 
  (chk_code_sen t aes aes_initial_list) = aes_stable_list.
Proof. 
  intros. induction H. vm_compute.  reflexivity.  
  unfold chk_code_sen. fold chk_code_sen. 
  rewrite IHle.
  apply aes_sen_stable.
Qed.

Fixpoint nth (n:nat) (l:list nat) {struct l} : nat :=
    match n, l with
      | O, x :: l' => x
      | O, other => 999
      | S m, nil => 999
      | S m, x :: t => nth m t
    end.

Theorem no_leaking_1 : nth done aes_stable_list = 0.
Proof.
  trivial.
Qed.

Theorem no_leaking_2 : nth text_out aes_stable_list = 0.
Proof.
  trivial.
Qed.
