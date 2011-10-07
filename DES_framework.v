(* A new framework to redefine the Verilog-Coq semantics model. 
Two problems will be solved here. First, the redefinition of the BUS model.
Second, module instantiation and modulized properties in large system. *)

(* I'll keep Eric's model if it still fits the new framework. For example, I'll keep the 
temporal logic for now. *)

Require Import Bool Arith List. 
Require Omega.

Inductive value := lo | hi.
Definition signal := nat -> value.
Definition VDD : signal := fun t : nat => hi.
Definition GND : signal := fun t : nat => lo.

Hypothesis lo_neq_hi : (lo = hi) = False.
Hypothesis hilo : forall x : value, x <> hi -> x = lo.
Hypothesis lohi : forall x : value, x <> lo -> x = hi.


Section Bus_Signals.

Definition bus_value := list value.
(*Definition busD := nat -> bus_value.
Definition busA := nat -> bus_value.  busA and busB are defined to represent downward and upward buses, i.e., 
  [63:0] desOut, [1:48] K_sub, respectively. *)

Inductive bus :=
  | busA : (nat -> bus_value) -> bus
  | busD : (nat -> bus_value) -> bus.

Definition bus_slice(b:bus)(p2 p1:nat):bus:=
  match b with 
  | busD d' => busD (fun t : nat => rev (firstn (p2-p1+1) (skipn p1 (rev (d' t)))))
  | busA a' => busA (fun t : nat => firstn (p1-p2+1) (skipn (p2-1) (a' t)))
  end.


Definition v := lo::lo::hi::hi::lo::nil.

Definition b := fun t:nat => v.
Definition b2 := busD (fun t:nat => v).

Eval compute in match (bus_slice (busD b) 4 0 ) with | busD a' => (a' 1) 
                                                     | busA a' => (a' 1) end.

Eval compute in match (bus_slice (busA b) 1 4 ) with | busD a' => (a' 1) 
                                                     | busA a' => (a' 1) end.

Eval compute in bus_slice b2 4 0.


(* Notation "b @( m , n ) " := (bus_slice b m n ) (at level 50, left associativity). *)
Notation "b [ m , n ] " := (bus_slice b m n ) (at level 50, left associativity).


Eval compute in  (b2 [4,1] [3,2]).


Definition bus_length (b : bus) :=
  fun t : nat => match b with 
                 | busA a' => length (a' t)
                 | busD d' => length (d' t)
                 end.

Eval compute in (bus_length (b2)).


Definition not (a : value) : value :=
  match a with
  | lo => hi
  | hi => lo
  end.

Eval compute in (not hi).

Definition sig_not (a : signal) : signal :=
  fun t : nat => match (a t) with
                 | lo => hi
                 | hi => lo
                 end.

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

(* BUS OPERATIONS. *)
Fixpoint bv_bit_not (a : bus_value) {struct a} : bus_value :=
  match a with
  | nil => nil
  | la :: a' => (not la) :: (bv_bit_not a')
  end.

Definition bus_bit_not (b : bus) : bus :=
  match b with
  | busD d' => busD (fun t:nat => bv_bit_not (d' t))
  | busA a' => busA (fun t:nat => bv_bit_not (a' t))
  end.

Eval compute in bus_bit_not (b2[3,1]).

Definition v2 := lo::hi::lo::lo::lo::nil.
Definition b3 := busD (fun t:nat => v2).


Fixpoint bv_bit_xor (a b : bus_value) {struct a} := 
  match a with
  | nil => nil
  | la :: a' => match b with
                | nil => nil
                | lb :: b' => (xor la lb) :: (bv_bit_xor a' b')
                end
  end.    (* here we assume the bus widths are the same *)

Definition bus_bit_xor (a b : bus) : bus :=
  match a with
  | busD ad' => match b with
               | busD bd' => busD (fun t:nat => bv_bit_xor (ad' t) (bd' t))
               | busA ba' => busD (fun t:nat => bv_bit_xor (ad' t) (rev (ba' t)))
               end
  | busA aa' => match b with
               | busD bd' => busD (fun t:nat => bv_bit_xor (rev (aa' t)) (bd' t))
               | busA ba' => busA (fun t:nat => bv_bit_xor (aa' t) (ba' t))
               end
  end.


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
  match a with 
  | busD ad' => match b with
                | busD bd' => busD (fun t:nat => bv_bit_and (ad' t) (bd' t))
                | busA ba' => busD (fun t:nat => bv_bit_and (ad' t) (rev (ba' t)))
                end
  | busA aa' => match b with
                | busD bd' => busD (fun t:nat => bv_bit_and (rev (aa' t)) (bd' t))
                | busA ba' => busA (fun t:nat => bv_bit_and (aa' t) (ba' t))
                end
  end.


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
  match a with 
  | busD ad' => match b with
                | busD bd' => busD (fun t:nat => bv_bit_or (ad' t) (bd' t))
                | busA ba' => busD (fun t:nat => bv_bit_or (ad' t) (rev (ba' t)))
                end
  | busA aa' => match b with
                | busD bd' => busD (fun t:nat => bv_bit_or (rev (aa' t)) (bd' t))
                | busA ba' => busA (fun t:nat => bv_bit_or (aa' t) (ba' t))
                end
  end.

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
  match a with 
               | busD ad' => match b with
                             | busD bd' => bv_eq (ad' t) (bd' t)
                             | busA ba' => bv_eq (ad' t) (rev (ba' t))
                             end
               | busA aa' => match b with
                             | busD bd' => bv_eq (rev (aa' t)) (bd' t)
                             | busA ba' => bv_eq (aa' t) (ba' t)
                             end
                end.

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
    match a with 
    | busD ad' => match b with
                  | busD bd' => bv_lt (ad' t) (bd' t)
                  | busA ba' => bv_lt (ad' t) (rev (ba' t))
                  end
    | busA aa' => match b with
                  | busD bd' => bv_lt (rev (aa' t)) (bd' t)
                  | busA ba' => bv_lt (aa' t) (ba' t)
                  end
    end.


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
  match a with 
  | busD ad' => match b with
                | busD bd' => bv_gt (ad' t) (bd' t)
                | busA ba' => bv_gt (ad' t) (rev (ba' t))
                end
  | busA aa' => match b with
                | busD bd' => bv_gt (rev (aa' t)) (bd' t)
                | busA ba' => bv_gt (aa' t) (ba' t)
                end
  end.

Fixpoint bv_eq_0 (a : bus_value) {struct a} : value :=
  match a with
  | hi :: lt => lo
  | lo :: lt => bv_eq_0 lt
  | nil => hi
  end.

Definition bus_eq_0 (a : bus) (t : nat) : value :=
  match a with 
  | busD ad' => bv_eq_0 (ad' t)
  | busA aa' => bv_eq_0 (aa' t)
  end.

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
  | econb b => match b with
               | busD bd => bd t
               | busA ab => ab t end
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

Section Assignment.

Definition assign_ex (a : bus) (e : expr) : bus :=
                  match a with
                  | busD ad => busD (eval e)
                  | busA aa => busA (eval e)
                  end.  (* Here the return value is also a bus. *)

Definition assign_b (a : bus) (b : bus) : bus :=
  match a with
  | busD ad => busD (eval (econb b))
  | busA aa => busA (eval (econb b))
  end.


Inductive  updateblock :=
  | upd : bus -> expr -> nat -> updateblock.

Definition update (u : updateblock) : updateblock :=
  match u with
  | upd b ex t => upd b ex (S t)
  end.

Definition eval_update (u : updateblock) : bus_value :=
  match u with
  | upd b ex t => eval ex t
  end.

(* We omit the function of eval_assign because it is the same as we eval a bus. *)                 



Lemma eval_upd : forall (a : bus) (ex : expr) (t : nat), eval_update (update (upd a ex t)) = eval_update (upd a ex (S t)).
Proof.
  intros.  tauto.
Qed.

Lemma assign_trans : forall (a b c : bus), assign_ex a (econb (assign_ex b (econb c))) = assign_ex a (econb c).
Proof.
  intros. unfold assign_ex. destruct a. unfold eval. destruct b0. 
  tauto. tauto. 
  destruct b0; tauto.
Qed.

Inductive caseblockb3 :=
  | cb : bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> bus -> caseblockb3.

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


Section key_selh.

Definition K_sub_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K_sub  : bus := busA (fun t : nat => K_sub_ini).

Definition K_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::nil.
Definition K : bus := busD (fun t:nat => K_ini).

Definition roundSel_ini := lo::lo::lo::lo::nil.
Definition roundSel : bus := busD (fun t:nat => roundSel_ini).

Definition decrypt : signal := fun t:nat => lo.

Definition K1_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K1 : bus := busA (fun t:nat => K1_ini).

Definition K2_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K2 : bus := busA (fun t:nat => K1_ini).

Definition K3_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K3 : bus := busA (fun t:nat => K1_ini).

Definition K4_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K4 : bus := busA (fun t:nat => K1_ini).

Definition K5_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K5 : bus := busA (fun t:nat => K1_ini).

Definition K6_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K6 : bus := busA (fun t:nat => K1_ini).

Definition K7_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K7 : bus := busA (fun t:nat => K1_ini).

Definition K8_ini := lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::lo::lo::
                                lo::lo::lo::lo::lo::lo::lo::lo::nil.
Definition K8 : bus := busA (fun t:nat => K1_ini).

Definition roundSelH_ini := lo::lo::lo::nil.
Definition roundSelH : bus := busD (fun t:nat => roundSelH_ini).

Definition decryptH : signal := fun t:nat => lo.


(assign_ex roundSelH (cond roundSel[3,3] enot(roundSel[2,0]) roundSel[2,0]))

assign_ex 














Lemma case_assign3_t3 : forall (a b1 b2 b3 b4 b5 b6 b7 b8 : bus), case_assign3 a (busD (fun _:nat=>lo::hi::lo::nil))
                          b1 b2 b3 b4 b5 b6 b7 b8 -> forall t : nat, (eval (econb a) t) = (eval (econb b3) t).
Proof.
  intros. unfold case_assign3 in H. unfold eval in H. unfold eval. destruct a; destruct b5;
  unfold assign in H; unfold eval in H; apply H; trivial.
Qed.

End Assignment.

Section Instantiation.



Section key_selh.

  
  

Definition update (a : bus ) (e : expr) :=
  fun t : nat => match a with
                 | busD ad => (ad t) = (eval e t)
                 | busA aa => (aa t) = (eval e t)
                 end.


Eval compute in (b2).
Eval compute in b2.


Lemma assign_refl : forall (t : nat) (a : bus) (e : expr), 
                    assign a e -> match a with
                                  | busD ad => ad t = eval e t
                                  | busA aa => aa t = eval e t
                                  end.
Proof.
  destruct a. intros. unfold assign in H. generalize t.
  intros. destruct a. unfold assign in H. apply H.

Definition update



Variables addr dout : bus.

Lemma dout_assign : forall t : nat, eval (

  

Definition assign (a : bus) (e : expr) : Prop :=
  forall t : nat, match a with
                  | busD d' => (d' t) = (eval e t)
                  | busA a' => (a' t) = (eval e t)
                  end.

End Assignment.

Section Sequential.

Inductive seq_upd_block :=
  | upd : bus -> bus -> nat -> seq_upd_block.

Definition seq_upd (b : seq_upd_block) :=
  forall t : nat, match b with
                  | upd b1 b2 t => match b1 with
                                   | busD b1d => match b2 with
                                                 | busD b2d => (b1d (S t)) = (b2d t) 
                                                 | busA b2a => (b1d (S t)) = (b2a t) 
                                                 end
                                   | busA b1a => match b2 with
                                                 | busD b2d => (b1a (S t)) = (b2d t)
                                                 | busA b2a => (b1a (S t)) = (b2a t)
                                                 end
                                   end
                   end.

End Sequential.

Section sbox1.


Section Instantiation.

Inductive inst_block :=
  | inst2: (bus -> bus) -> (bus -> bus) -> inst_block
  | inst3: (bus -> bus) -> (bus -> bus) -> (bus -> bus) -> inst_block
  | inst4: (bus -> bus) -> (bus -> bus) -> (bus -> bus) -> (bus -> bus) -> inst_block.

Definition instantilize (i : inst_block) :=
  forall t : nat => match i with
                    | inst2 map1 map2 => 



(* The DES circuit *)
Section DES_core.





Variable tt : bus.
Check tt.
Print tt.
Eval compute in tt.































