(* This is the first try on AES encryption core with the denotation derived from "DES_cycle_nat_des5.v".
The Verilog code is, again, the Rudolf version downloaded from Opencores. Similar to the example of DES core 
I used for VTS 2012, it is not a good sample for a pipleline design. It is, in reality, a one stage (area optimized)
AES encryption core with a internal loop control (a downward counter). 
So similar methods tracking information flow developed in DES core should apply here in AES.

And, hopefully, this method can be expanded to deep pipelined designs and processor level feedback designs. 1/10/2012
*)


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
  | eand_bit : bus -> expr      (* bit wise operation on buses /AES/*)
  | eor_bit : bus -> expr	(* /AES/*)
  | exor_bit : bus -> expr	(* /AES/*)
  | eplus : expr -> expr -> expr 	(* PLUS operation between buses and constant /AES/*)
  | eminus : expr -> expr -> expr	(* MINUS operation /AES/*)
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
  | eand_bit b => nth b sl 0 (* bit wise operation on buses do not change the sensivity of the bus /AES/*)
  | eor_bit b => nth b sl 0  (* /AES/ *)
  | exor_bit b => nth b sl 0 (* /AES/ *)
  | eplus ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)  (* /AES/ *)
  | eminus ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl) (* /AES/ *)
  | enot ex => expr_sen_eval ex sl
  | eapp b1 b2 => boptag (nth b1 (sl) 0) (nth b2 (sl) 0)
  | cond cex ex1 ex2 => boptag (expr_sen_eval ex1 sl) (expr_sen_eval ex2 sl)
  | perm ex => lowertag (expr_sen_eval ex sl)
  | exor_key ex key => lowertag (expr_sen_eval ex sl)  (* The only operation in AES to decrease sensitivity level except sub-module. *)
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


(* ********************************************************************
/////////////////////////////////////////////////////////////////////
////                                                             ////
////  AES Cipher Top Level                                       ////
////                                                             ////
////                                                             ////
////  Author: Rudolf Usselmann                                   ////
////          rudi@asics.ws                                      ////
////                                                             ////
////                                                             ////
////  Downloaded from: http://www.opencores.org/cores/aes_core/  ////
////                                                             ////
/////////////////////////////////////////////////////////////////////
////                                                             ////
//// Copyright (C) 2000-2002 Rudolf Usselmann                    ////
////                         www.asics.ws                        ////
////                         rudi@asics.ws                       ////
////                                                             ////
//// This source file may be used and distributed without        ////
//// restriction provided that this copyright statement is not   ////
//// removed from the file and that any derivative work contains ////
//// the original copyright notice and the associated disclaimer.////
////                                                             ////
////     THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY     ////
//// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED   ////
//// TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS   ////
//// FOR A PARTICULAR PURPOSE. IN NO EVENT SHALL THE AUTHOR      ////
//// OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,         ////
//// INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES    ////
//// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE   ////
//// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        ////
//// BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF  ////
//// LIABILITY, WHETHER IN  CONTRACT, STRICT LIABILITY, OR TORT  ////
//// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT  ////
//// OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         ////
//// POSSIBILITY OF SUCH DAMAGE.                                 ////
////                                                             ////
/////////////////////////////////////////////////////////////////////

//  CVS Log
//
//  $Id: aes_cipher_top.v,v 1.1.1.1 2002-11-09 11:22:48 rudi Exp $
//
//  $Date: 2002-11-09 11:22:48 $
//  $Revision: 1.1.1.1 $
//  $Author: rudi $
//  $Locker:  $
//  $State: Exp $
//
// Change History:
//               $Log: not supported by cvs2svn $
//
//
//
//
//

`include "timescale.v"

module aes_cipher_top(clk, rst, ld, done, key, text_in, text_out );
input		clk, rst;
input		ld;
output		done;
input	[127:0]	key;
input	[127:0]	text_in;
output	[127:0]	text_out;

////////////////////////////////////////////////////////////////////
//
// Local Wires
//

wire	[31:0]	w0, w1, w2, w3;
reg	[127:0]	text_in_r;
reg	[127:0]	text_out;
reg	[7:0]	sa00, sa01, sa02, sa03;
reg	[7:0]	sa10, sa11, sa12, sa13;
reg	[7:0]	sa20, sa21, sa22, sa23;
reg	[7:0]	sa30, sa31, sa32, sa33;
wire	[7:0]	sa00_next, sa01_next, sa02_next, sa03_next;
wire	[7:0]	sa10_next, sa11_next, sa12_next, sa13_next;
wire	[7:0]	sa20_next, sa21_next, sa22_next, sa23_next;
wire	[7:0]	sa30_next, sa31_next, sa32_next, sa33_next;
wire	[7:0]	sa00_sub, sa01_sub, sa02_sub, sa03_sub;
wire	[7:0]	sa10_sub, sa11_sub, sa12_sub, sa13_sub;
wire	[7:0]	sa20_sub, sa21_sub, sa22_sub, sa23_sub;
wire	[7:0]	sa30_sub, sa31_sub, sa32_sub, sa33_sub;
wire	[7:0]	sa00_sr, sa01_sr, sa02_sr, sa03_sr;
wire	[7:0]	sa10_sr, sa11_sr, sa12_sr, sa13_sr;
wire	[7:0]	sa20_sr, sa21_sr, sa22_sr, sa23_sr;
wire	[7:0]	sa30_sr, sa31_sr, sa32_sr, sa33_sr;
wire	[7:0]	sa00_mc, sa01_mc, sa02_mc, sa03_mc;
wire	[7:0]	sa10_mc, sa11_mc, sa12_mc, sa13_mc;
wire	[7:0]	sa20_mc, sa21_mc, sa22_mc, sa23_mc;
wire	[7:0]	sa30_mc, sa31_mc, sa32_mc, sa33_mc;
reg		done, ld_r;
reg	[3:0]	dcnt;

////////////////////////////////////////////////////////////////////
//
// Misc Logic
//

always @(posedge clk)
	if(!rst)	dcnt <= #1 4'h0;
	else
	if(ld)		dcnt <= #1 4'hb;
	else
	if(|dcnt)	dcnt <= #1 dcnt - 4'h1;

always @(posedge clk) done <= #1 !(|dcnt[3:1]) & dcnt[0] & !ld;
always @(posedge clk) if(ld) text_in_r <= #1 text_in;
always @(posedge clk) ld_r <= #1 ld;

////////////////////////////////////////////////////////////////////
//
// Initial Permutation (AddRoundKey)
//

always @(posedge clk)	sa33 <= #1 ld_r ? text_in_r[007:000] ^ w3[07:00] : sa33_next;
always @(posedge clk)	sa23 <= #1 ld_r ? text_in_r[015:008] ^ w3[15:08] : sa23_next;
always @(posedge clk)	sa13 <= #1 ld_r ? text_in_r[023:016] ^ w3[23:16] : sa13_next;
always @(posedge clk)	sa03 <= #1 ld_r ? text_in_r[031:024] ^ w3[31:24] : sa03_next;
always @(posedge clk)	sa32 <= #1 ld_r ? text_in_r[039:032] ^ w2[07:00] : sa32_next;
always @(posedge clk)	sa22 <= #1 ld_r ? text_in_r[047:040] ^ w2[15:08] : sa22_next;
always @(posedge clk)	sa12 <= #1 ld_r ? text_in_r[055:048] ^ w2[23:16] : sa12_next;
always @(posedge clk)	sa02 <= #1 ld_r ? text_in_r[063:056] ^ w2[31:24] : sa02_next;
always @(posedge clk)	sa31 <= #1 ld_r ? text_in_r[071:064] ^ w1[07:00] : sa31_next;
always @(posedge clk)	sa21 <= #1 ld_r ? text_in_r[079:072] ^ w1[15:08] : sa21_next;
always @(posedge clk)	sa11 <= #1 ld_r ? text_in_r[087:080] ^ w1[23:16] : sa11_next;
always @(posedge clk)	sa01 <= #1 ld_r ? text_in_r[095:088] ^ w1[31:24] : sa01_next;
always @(posedge clk)	sa30 <= #1 ld_r ? text_in_r[103:096] ^ w0[07:00] : sa30_next;
always @(posedge clk)	sa20 <= #1 ld_r ? text_in_r[111:104] ^ w0[15:08] : sa20_next;
always @(posedge clk)	sa10 <= #1 ld_r ? text_in_r[119:112] ^ w0[23:16] : sa10_next;
always @(posedge clk)	sa00 <= #1 ld_r ? text_in_r[127:120] ^ w0[31:24] : sa00_next;

////////////////////////////////////////////////////////////////////
//
// Round Permutations
//

assign sa00_sr = sa00_sub;
assign sa01_sr = sa01_sub;
assign sa02_sr = sa02_sub;
assign sa03_sr = sa03_sub;
assign sa10_sr = sa11_sub;
assign sa11_sr = sa12_sub;
assign sa12_sr = sa13_sub;
assign sa13_sr = sa10_sub;
assign sa20_sr = sa22_sub;
assign sa21_sr = sa23_sub;
assign sa22_sr = sa20_sub;
assign sa23_sr = sa21_sub;
assign sa30_sr = sa33_sub;
assign sa31_sr = sa30_sub;
assign sa32_sr = sa31_sub;
assign sa33_sr = sa32_sub;
assign {sa00_mc, sa10_mc, sa20_mc, sa30_mc}  = mix_col(sa00_sr,sa10_sr,sa20_sr,sa30_sr);
assign {sa01_mc, sa11_mc, sa21_mc, sa31_mc}  = mix_col(sa01_sr,sa11_sr,sa21_sr,sa31_sr);
assign {sa02_mc, sa12_mc, sa22_mc, sa32_mc}  = mix_col(sa02_sr,sa12_sr,sa22_sr,sa32_sr);
assign {sa03_mc, sa13_mc, sa23_mc, sa33_mc}  = mix_col(sa03_sr,sa13_sr,sa23_sr,sa33_sr);
assign sa00_next = sa00_mc ^ w0[31:24];
assign sa01_next = sa01_mc ^ w1[31:24];
assign sa02_next = sa02_mc ^ w2[31:24];
assign sa03_next = sa03_mc ^ w3[31:24];
assign sa10_next = sa10_mc ^ w0[23:16];
assign sa11_next = sa11_mc ^ w1[23:16];
assign sa12_next = sa12_mc ^ w2[23:16];
assign sa13_next = sa13_mc ^ w3[23:16];
assign sa20_next = sa20_mc ^ w0[15:08];
assign sa21_next = sa21_mc ^ w1[15:08];
assign sa22_next = sa22_mc ^ w2[15:08];
assign sa23_next = sa23_mc ^ w3[15:08];
assign sa30_next = sa30_mc ^ w0[07:00];
assign sa31_next = sa31_mc ^ w1[07:00];
assign sa32_next = sa32_mc ^ w2[07:00];
assign sa33_next = sa33_mc ^ w3[07:00];

////////////////////////////////////////////////////////////////////
//
// Final text output
//

always @(posedge clk) text_out[127:120] <= #1 sa00_sr ^ w0[31:24];
always @(posedge clk) text_out[095:088] <= #1 sa01_sr ^ w1[31:24];
always @(posedge clk) text_out[063:056] <= #1 sa02_sr ^ w2[31:24];
always @(posedge clk) text_out[031:024] <= #1 sa03_sr ^ w3[31:24];
always @(posedge clk) text_out[119:112] <= #1 sa10_sr ^ w0[23:16];
always @(posedge clk) text_out[087:080] <= #1 sa11_sr ^ w1[23:16];
always @(posedge clk) text_out[055:048] <= #1 sa12_sr ^ w2[23:16];
always @(posedge clk) text_out[023:016] <= #1 sa13_sr ^ w3[23:16];
always @(posedge clk) text_out[111:104] <= #1 sa20_sr ^ w0[15:08];
always @(posedge clk) text_out[079:072] <= #1 sa21_sr ^ w1[15:08];
always @(posedge clk) text_out[047:040] <= #1 sa22_sr ^ w2[15:08];
always @(posedge clk) text_out[015:008] <= #1 sa23_sr ^ w3[15:08];
always @(posedge clk) text_out[103:096] <= #1 sa30_sr ^ w0[07:00];
always @(posedge clk) text_out[071:064] <= #1 sa31_sr ^ w1[07:00];
always @(posedge clk) text_out[039:032] <= #1 sa32_sr ^ w2[07:00];
always @(posedge clk) text_out[007:000] <= #1 sa33_sr ^ w3[07:00];

////////////////////////////////////////////////////////////////////
//
// Generic Functions
//

function [31:0] mix_col;
input	[7:0]	s0,s1,s2,s3;
reg	[7:0]	s0_o,s1_o,s2_o,s3_o;
begin
mix_col[31:24]=xtime(s0)^xtime(s1)^s1^s2^s3;
mix_col[23:16]=s0^xtime(s1)^xtime(s2)^s2^s3;
mix_col[15:08]=s0^s1^xtime(s2)^xtime(s3)^s3;
mix_col[07:00]=xtime(s0)^s0^s1^s2^xtime(s3);
end
endfunction

function [7:0] xtime;
input [7:0] b; xtime={b[6:0],1'b0}^(8'h1b&{8{b[7]}});
endfunction

////////////////////////////////////////////////////////////////////
//
// Modules
//

aes_key_expand_128 u0(
	.clk(		clk	),
	.kld(		ld	),
	.key(		key	),
	.wo_0(		w0	),
	.wo_1(		w1	),
	.wo_2(		w2	),
	.wo_3(		w3	));

aes_sbox us00(	.a(	sa00	), .d(	sa00_sub	));
aes_sbox us01(	.a(	sa01	), .d(	sa01_sub	));
aes_sbox us02(	.a(	sa02	), .d(	sa02_sub	));
aes_sbox us03(	.a(	sa03	), .d(	sa03_sub	));
aes_sbox us10(	.a(	sa10	), .d(	sa10_sub	));
aes_sbox us11(	.a(	sa11	), .d(	sa11_sub	));
aes_sbox us12(	.a(	sa12	), .d(	sa12_sub	));
aes_sbox us13(	.a(	sa13	), .d(	sa13_sub	));
aes_sbox us20(	.a(	sa20	), .d(	sa20_sub	));
aes_sbox us21(	.a(	sa21	), .d(	sa21_sub	));
aes_sbox us22(	.a(	sa22	), .d(	sa22_sub	));
aes_sbox us23(	.a(	sa23	), .d(	sa23_sub	));
aes_sbox us30(	.a(	sa30	), .d(	sa30_sub	));
aes_sbox us31(	.a(	sa31	), .d(	sa31_sub	));
aes_sbox us32(	.a(	sa32	), .d(	sa32_sub	));
aes_sbox us33(	.a(	sa33	), .d(	sa33_sub	));

endmodule


******************************************************** *)
Definition clk : bus		:= 0.
Definition rst : bus		:= 1.
Definition ld : bus		:= 2.
Definition key : bus		:= 3.
Definition text_in : bus	:= 4.
Definition w : bus		:= 5.
Definition w0 : bus		:= 6.
Definition w1 : bus		:= 7.
Definition w2 : bus		:= 8.
Definition w3 : bus		:= 9.
Definition w4 : bus		:= 10.
Definition text_in_r : bus	:= 11.
Definition sa00 : bus		:= 12.
Definition sa01: bus		:= 13.
Definition sa02 : bus		:= 14.
Definition sa03 : bus		:= 15.
Definition sa10 : bus		:= 16.
Definition sa11 : bus		:= 17.
Definition sa12 : bus		:= 18.
Definition sa13 : bus		:= 19.
Definition sa20 : bus		:= 20.
Definition sa21 : bus		:= 21.
Definition sa22 : bus		:= 22.
Definition sa23 : bus		:= 23.
Definition sa30 : bus		:= 24.
Definition sa31 : bus		:= 25.
Definition sa32 : bus		:= 26.
Definition sa33 : bus		:= 27.
Definition  : bus		:= 28.
Definition clk : bus		:= 29.
Definition clk : bus		:= 30.
Definition clk : bus		:= 31.
Definition clk : bus		:= 32.
Definition clk : bus		:= 33.
Definition clk : bus		:= 34.
Definition clk : bus		:= 35.
Definition clk : bus		:= 36.
Definition clk : bus		:= 37.
Definition clk : bus		:= 38.
Definition clk : bus		:= 39.
Definition clk : bus		:= 40.
Definition clk : bus		:= 41.
Definition clk : bus		:= 42.



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







