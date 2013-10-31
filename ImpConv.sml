(* ========================================================================= *)
(*                                                                           *)
(*                 Implicational conversions.                                *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Analysis and Design of Dependable Systems                *)
(*                  fortiss GmbH, Munich, Germany                            *)
(*                                                                           *)
(*       Formerly:  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent.aravantinos@fortiss.org>                      *)
(*                                                                           *)
(* ========================================================================= *)

structure ImpConv =
struct

open HolKernel Parse boolLib ImpConvUtils;

(*****************************************************************************)
(* IMPLICATIONAL RULES                                                       *)
(* i.e., rules to build propositions based on implications rather than       *)
(* equivalence.                                                              *)
(*****************************************************************************)

val MONO_AND' = TAUT `(A ==> B) /\ (C ==> D) ==> A /\ C ==> B /\ D`;
val MONO_OR' = TAUT `(A ==> B) /\ (C ==> D) ==> A \/ C ==> B \/ D`;
val MONO_IMP' = TAUT `(A ==> B) /\ (C ==> D) ==> A ==> C ==> B ==> D`;
val MONO_NOT' = TAUT `(B ==> A) ==> ~A ==> ~B`;

fun MKIMP_common lem th1 th2 =
  let 
    val (a,b) = dest_imp_only (concl th1)
    val (c,d) = dest_imp_only (concl th2)
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end;

(* Similar to [MK_CONJ] but theorems should be implicational instead of
 * equational, i.e., conjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A /\ C ==> B /\ D].
 *)
val MKIMP_CONJ = MKIMP_common MONO_AND';

(* Similar to [MK_DISJ] but theorems should be implicational instead of
 * equational, i.e., disjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A \/ C ==> B \/ D].
 *)
val MKIMP_DISJ = MKIMP_common MONO_OR';

local
  val lem = 
    TAUT `((A ==> B) ==> (C ==> D)) /\ ((B ==> A) ==> (D ==> C)) ==>
      (A <=> B) ==> (C <=> D)`
in
fun MKIMP_IFF th1 th2 =
  let 
    val (ab,cd) = dest_imp_only (concl th1)
    val (a,b) = dest_imp_only ab
    val (c,d) = dest_imp_only cd
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

(* th1 = (A ==> B) ==> C1
 * th2 = (B ==> A) ==> C2
 * output = (A <=> B) ==> (C1 /\ C2)
 *)
local
  val lem = TAUT
    `((A ==> B) ==> C) /\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\ D`
in
fun MKIMP_CONTRA_IFF th1 th2 =
  let
    val (ab,c) = dest_imp_only (concl th1)
    val d = snd (dest_imp_only (concl th2))
    val (a,b) = dest_imp_only ab
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

local val lem = TAUT `((A ==> B) ==> C) ==> (A <=> B) ==> C /\ (B ==> A)` in
fun MKIMPL_CONTRA_IFF th =
  let 
    val (ab,c) = dest_imp_only (concl th)
    val (a,b) = dest_imp_only ab
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c)] lem) th
  end
end;

local val lem = TAUT `((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\ D` in
fun MKIMPR_CONTRA_IFF th =
  let 
    val (ba,d) = dest_imp_only (concl th)
    val (b,a) = dest_imp_only ba
  in
    MP (INST [(A_|->a),(B_|->b),(D_|->d)] lem) th
  end
end;

local
  val lem = 
    TAUT `(C ==> A ==> B) /\ (D ==> B ==> A) ==> C /\ D ==> (A <=> B)`
in
fun MKIMP_CO_IFF th1 th2 =
  let 
    val (c,ab) = dest_imp_only (concl th1)
    val (d,_) = dest_imp_only (concl th2)
    val (a,b) = dest_imp_only ab
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

local val lem = TAUT `(C ==> A ==> B) ==> C /\ (B ==> A) ==> (A <=> B)` in
fun MKIMPL_CO_IFF th =
  let
    val (c,ab) = dest_imp_only (concl th)
    val (a,b) = dest_imp_only ab
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c)] lem) th
  end
end;

local val lem = TAUT `(D ==> B ==> A) ==> (A ==> B) /\ D ==> (A <=> B)` in
fun MKIMPR_CO_IFF th =
  let 
    val (d,ba) = dest_imp_only (concl th)
    val (b,a) = dest_imp_only ba
  in
    MP (INST [(A_|->a),(B_|->b),(D_|->d)] lem) th
  end
end;

(* Given two theorems [A ==> B] and [C ==> D],
 * returns [(B ==> C) ==> (A ==> D)].
 *)
fun MKIMP_IMP th1 th2 =
  let 
    val (b,a) = dest_imp_only (concl th1)
    val (c,d) = dest_imp_only (concl th2)
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] MONO_IMP') (CONJ th1 th2)
  end;

fun MKIMPL_common' lem th t =
  let val (a,b) = dest_imp_only (concl th) in
  MP (INST [(A_|->a),(B_|->b),(C_|->t)] lem) th
  end;

fun MKIMPL_common lem th t =
  MKIMPL_common' (REWRITE_RULE[] (INST [D_|->C_] lem)) th t;

(* Given a theorem [A ==> B] and a term [C],
 * returns [A /\ C ==> B /\ C].
 *)
val MKIMPL_CONJ = MKIMPL_common MONO_AND';

(* Given a theorem [A ==> B] and a term [C],
 * returns [A \/ C ==> B \/ C].
 *)
val MKIMPL_DISJ = MKIMPL_common MONO_OR';

(* Given a theorem [A ==> B] and a term [C],
 * returns [(B ==> C) ==> (A ==> C)].
 *)
local val MONO_IMP'' = REWRITE_RULE[] (INST [D_|->C_] MONO_IMP') in
fun MKIMPL_IMP th t =
  let val (b,a) = dest_imp_only (concl th) in
    MP (INST [(A_|->a),(B_|->b),(C_|->t)] MONO_IMP'') th
  end
end;

fun MKIMPR_common' lem t th =
  let val (c,d) = dest_imp_only (concl th) in
    MP (INST [(C_|->c),(D_|->d),(A_|->t)] lem) th
  end;

fun MKIMPR_common lem t th =
  MKIMPR_common' (REWRITE_RULE[] (INST [B_|->A_] lem)) t th;

(* Given a term [A] and a theorem [B ==> C],
 * returns [A /\ B ==> A /\ C].
 *)
val MKIMPR_CONJ = MKIMPR_common MONO_AND';

(* Given a term [A] and a theorem [B ==> C],
 * returns [A \/ B ==> A \/ C].
 *)
val MKIMPR_DISJ = MKIMPR_common MONO_OR';

(* Given a term [A] and a theorem [B ==> C],
 * returns [(A ==> B) ==> (A ==> C)].
 *)
val MKIMPR_IMP = MKIMPR_common MONO_IMP';

(* Given a theorem [A ==> B], returns [~B ==> ~A]. *)
fun MKIMP_NOT th =
  let val (b,a) = dest_imp_only (concl th) in
    MP (INST [(A_|->a),(B_|->b)] MONO_NOT') th
  end;

fun MKIMP_QUANT lem x th =
  let 
    val x_ty = type_of x
    val (p,q) = dest_imp_only (concl th)
    val p' = mk_abs(x,p)
    val q' = mk_abs(x,q)
    val P = mk_var("P",mk_fun_ty x_ty bool_ty)
    val Q = mk_var("Q",mk_fun_ty x_ty bool_ty)
    val lem = INST [(P|->p'),(Q|->q')] (INST_TYPE [aty|->x_ty] lem)
    val c = ONCE_DEPTH_CONV (ALPHA_CONV x) THENC ONCE_DEPTH_CONV BETA_CONV
  in
    MP (CONV_RULE c lem) (GEN x th)
  end;

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(!x. A) ==> (!x. B)]. *)
val MKIMP_FORALL = MKIMP_QUANT MONO_FORALL;

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(?x. A) ==> (?x. B)]. *)
val MKIMP_EXISTS = MKIMP_QUANT MONO_EXISTS;

(* Given two theorems [A ==> B] and [B ==> C ==> D],
 * returns [(B ==> C) ==> (A ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
local val lem = TAUT `(B==>A) /\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)` in
fun MKIMP_IMP_CONTRA_CTXT th1 th2 =
  let 
    val (a,bcd) = dest_imp_only (concl th2)
    val (b,cd) = dest_imp_only bcd
    val (c,d) = dest_imp_only cd
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

local val lem = TAUT `(A==>B) /\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)` in
fun MKIMP_IMP_CO_CTXT th1 th2 =
  let 
    val (a,bdc) = dest_imp_only (concl th2)
    val (b,dc) = dest_imp_only bdc
    val (d,c) = dest_imp_only dc
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

(* Given a theorem [B ==> C ==> D], returns [(B ==> C) ==> (B ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
local val lem = TAUT `(A==>C==>D) ==> (A==>C) ==> (A==>D)` in
fun MKIMPR_IMP_CTXT th =
  let
    val (a,cd) = dest_imp_only (concl th)
    val (c,d) = dest_imp_only cd
  in
    MP (INST [(C_|->c),(D_|->d),(A_|->a)] lem) th
  end
end;

(* Given two theorems [A ==> B] and [A ==> B ==> C ==> D],
 * returns [(A /\ C) ==> (B /\ D)],
 * i.e., similar to [MKIMP_CONJ] but allows to remove the contexts [A] and [B].
 *)
local val lem = TAUT `(C==>A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)` in
fun MKIMP_CONJ_CONTRA_CTXT th1 th2 =
  let
    val (a,bcd) = dest_imp_only (concl th2)
    val (b,cd) = dest_imp_only bcd
    val (c,d) = dest_imp_only cd
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

local val lem = TAUT `(C==>A==>B) ==> (A/\C==>B/\C)` in
fun MKIMPL_CONJ_CONTRA_CTXT th =
  let
    val (c,ab) = dest_imp_only (concl th)
    val (a,b) = dest_imp_only ab
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c)] lem) th
  end
end;

local val lem = TAUT `(A==>C==>D) ==> (A/\C==>A/\D)` in
fun MKIMPR_CONJ_CONTRA_CTXT th =
  let 
    val (a,cd) = dest_imp_only (concl th)
    val (c,d) = dest_imp_only cd
  in
    MP (INST [(A_|->a),(C_|->c),(D_|->d)] lem) th
  end
end;

local val lem = TAUT `(B==>A) /\ (B==>D==>C) ==> (B/\D==>A/\C)` in
fun MKIMP_CONJ_CO_CTXT th1 th2 =
  let 
    val (b,a) = dest_imp_only (concl th1)
    val (d,c) = dest_imp_only (snd (dest_imp_only (concl th2)))
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c),(D_|->d)] lem) (CONJ th1 th2)
  end
end;

local val lem = TAUT `(B==>A) ==> (B/\C==>A/\C)` in
fun MKIMPL_CONJ_CO_CTXT th =
  let val (b,a) = dest_imp_only (concl th) in
    fn c => MP (INST [(A_|->a),(B_|->b),(C_|->c)] lem) th
  end
end;

local val lem = TAUT `(C==>B==>A) ==> (B/\C==>A/\C)` in
fun MKIMPL_CONJ_CO2_CTXT th =
  let
    val (c,ba) = dest_imp_only (concl th)
    val (b,a) = dest_imp_only ba
  in
    MP (INST [(A_|->a),(B_|->b),(C_|->c)] lem) th
  end
end;

val MKIMPR_CONJ_CO_CTXT = MKIMPR_CONJ_CONTRA_CTXT;


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS                                                 *)
(*****************************************************************************)

structure Variance =
  struct
    datatype t = Co | Contra
    fun neg Co = Contra | neg Contra = Co
  end;

open Variance;

(* An implicational conversion maps a term t to a theorem of the form:
 * t' ==> t if covariant
 * t ==> t' if contravariant
 *)
type imp_conv = Variance.t -> term -> thm;

(* Trivial embedding of conversions into implicational conversions. *)
fun imp_conv_of_conv c v t =
  let val (th1,th2) = EQ_IMP_RULE (c t) in
    case v of Co => th2 | Contra => th1
  end;

(* Retrieves the outcome of an implicational conversion, i.e., t'. *)
fun imp_conv_outcome th v =
  let val (t1,t2) = dest_binary_blind (concl th) in
    case v of Co => t1 | Contra => t2
  end;

(* [ALL_IMPCONV _ t] returns ``t==>t`` *)
val ALL_IMPCONV:imp_conv = fn _ => IMP_REFL;

(* The implicational conversion which always fails. *)
val NO_IMPCONV:imp_conv = fn _ => fn _ => failwith "NO_IMPCONV";

fun bind_impconv (c:imp_conv) v th =
  let val (t1,t2) = dest_imp_only (concl th) in
    case v of
    Co => IMP_TRANS (c v t1) th
    |Contra => IMP_TRANS th (c v t2)
  end;

fun THEN_IMPCONV (c1:imp_conv) c2 v t = bind_impconv c2 v (c1 v t);


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Given a theorem [p ==> c], returns the implicational conversion which:
  * - in the covariant case, matches the input term [t] against [c] and returns
  *   [s(p) ==> t], where [s] is the matching substitution
  * - in the contravariant case, matches the input term [t] against [p] and returns
  *   [t ==> s(c)], where [s] is the matching substitution
  *)
val MATCH_MP_IMPCONV:thm->imp_conv =
  fn th =>
    fn Co => GEN_PART_MATCH rand th
    | Contra => GEN_PART_MATCH lhand th;


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* From an implicational conversion builds a rule, i.e., a function which
 * takes a theorem and returns a new theorem.
 *)
val IMPCONV_RULE:imp_conv->thm->thm =
  fn c => fn th =>
    let val t = concl th in
      MATCH_MP (c Contra t) th
    end;

(* From an implicational conversion builds a tactic. *)
fun IMPCONV_TAC cnv (g as (_,c)) =
    (MATCH_MP_TAC (cnv Co c) THEN TRY (ACCEPT_TAC TRUTH)) g;


(*****************************************************************************)
(* CONTEXT HANDLING                                                          *)
(*****************************************************************************)

(* [term list] = terms to add to the context *)
datatype 'a with_context =
  With_context of 'a * (Tset.t -> 'a with_context) * (term -> 'a with_context);

fun apply (With_context(c,_,_)) = c;

(* Maybe avoid the augment if the input list is empty? *)
fun augment (With_context(_,a,_)) = a;
fun diminish (With_context(_,_,d)) = d;
fun apply_with_context c ctx v t =
  DISCH_CONJ ctx (apply (augment c (Tset.strip_conj ctx)) v t);

val imp_conv_of_ctx_imp_conv = (apply:imp_conv with_context -> imp_conv);

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ C)] returns [B /\ D ==> A /\ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [CONJ_IMPCONV ic1 ic2 Contra (A /\ B)]
 * returns [A /\ B ==> C /\ D].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [A |- D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ B)] returns [|- C /\ D ==> A /\ B]
 * (i.e., [A] does not appear in the hypotheses).
 *)
fun CONJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      let val (t1,t2) = dest_conj t in
      case v of
      Co =>
        (let val th1 = apply c Co t1 in
          let val t1' = imp_conv_outcome th1 Co in
            MKIMP_CONJ_CO_CTXT th1 (apply_with_context c t1' Co t2)
          end
          handle HOL_ERR _ => MKIMPL_CONJ_CO_CTXT th1 t2
        end
        handle HOL_ERR _ => MKIMPR_CONJ_CO_CTXT (apply_with_context c t1 Co t2))
      |Contra =>
            (* note: we remove t1 in case it appears in t2, since otherwise,
             * t1 removes t2 and t2 removes t1
             *)
            let 
              val t2s = Tset.remove (Tset.strip_conj t2) t1
              val th1 = apply (augment c t2s) Contra t1
            in
              let 
                val t1' = imp_conv_outcome th1 Contra
                val t1s = Tset.strip_conj t1
                val t1s' = Tset.strip_conj t1'
                val t1s'' = Tset.union t1s t1s'
                val th2 = apply (augment c t1s'') Contra t2
                val th2' = DISCH_CONJ t1 (DISCH_CONJ t1' th2)
              in
                MKIMP_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1) th2'
              end
              handle HOL_ERR _ => MKIMPL_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1)
            end
            handle HOL_ERR _ => 
              MKIMPR_CONJ_CONTRA_CTXT (apply_with_context c t1 Contra t2)
      end)
      :imp_conv),
    CONJ_CTXIMPCONV o augment c,
    CONJ_CTXIMPCONV o diminish c);

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [DISJ_IMPCONV ic1 ic2 Co (A \/ C)] returns [B \/ D ==> A \/ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]
 * returns [A \/ B ==> C \/ D].
 *)
fun DISJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      let val (t1,t2) = dest_disj t in
        let val th1 = apply c v t1 in
          MKIMP_DISJ th1 (apply c v t2) handle HOL_ERR _ => MKIMPL_DISJ th1 t2
        end
        handle HOL_ERR _ => MKIMPR_DISJ t1 (apply c v t2)
      end):imp_conv),
    DISJ_CTXIMPCONV o augment c,
    DISJ_CTXIMPCONV o diminish c);

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Co C] returns [D ==> C],
 * then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns [(B ==> D) ==> (A ==> C)].
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Contra C] returns
 * [C ==> D], then [IMP_IMPCONV ic1 ic2 Contra (A ==> C)]
 * returns [(A ==> C) ==> (B ==> D)].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [B |- D ==> C], then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns
 * [|- (B ==> D) ==> (A ==> C)] (i.e., [B] does not appear in the hypotheses).
 *)
fun IMP_CTXIMPCONV (c:imp_conv with_context)  =
  With_context(
    ((fn v => fn t =>
      let val (t1,t2) = dest_imp_only t in
        let 
          val v' = Variance.neg v
          val th1 = apply c v' t1
          val t1' = imp_conv_outcome th1 v'
          val t1s = Tset.union (Tset.strip_conj t1) (Tset.strip_conj t1')
          val c' = augment c t1s
          val mk =
            case v of Co => MKIMP_IMP_CO_CTXT | Contra => MKIMP_IMP_CONTRA_CTXT
        in
          mk th1 (DISCH_CONJ t1 (DISCH_CONJ t1' (apply c' v t2)))
          handle HOL_ERR _ => MKIMPL_IMP th1 t2
        end
        handle HOL_ERR _ => MKIMPR_IMP_CTXT (apply_with_context c t1 v t2)
      end):imp_conv),
    IMP_CTXIMPCONV o augment c,
    IMP_CTXIMPCONV o diminish c);

fun IFF_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      let 
        val (t1,t2) = dest_iff t
        val (lr,l,r) =
        case v of
        Co => (MKIMP_CO_IFF,MKIMPL_CO_IFF,MKIMPR_CO_IFF)
        |Contra => (MKIMP_CONTRA_IFF,MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF)
      in
        (let val th1 = apply c v (mk_imp (t1,t2)) in
          let val th2 = apply c v (mk_imp (t2,t1)) in
            MKIMP_IFF th1 th2 handle HOL_ERR _ => lr th1 th2
          end
          handle HOL_ERR _ => l th1
        end
        handle HOL_ERR _ => r (apply c v (mk_imp (t2,t1))))
      end):imp_conv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c);

(* Consider an implicational conversion ic.
 * Suppose [ic Contra A] returns [A ==> B]
 * then [NOT_IMPCONV ic Co ~A] returns [~B ==> ~A].
 * Suppose [ic Co A] returns [B ==> A]
 * then [NOT_IMPCONV ic Contra ~A] returns [~A ==> ~B].
 *)
fun NOT_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      MKIMP_NOT (apply c (Variance.neg v) (dest_neg t))):imp_conv),
    NOT_CTXIMPCONV o augment c,
    NOT_CTXIMPCONV o diminish c);

fun QUANT_CTXIMPCONV mkimp sel (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      let 
        val (x,b) = sel t
        val c' = diminish c x
      in
        mkimp x (apply c' v b)
      end):imp_conv),
    QUANT_CTXIMPCONV mkimp sel o augment c,
    QUANT_CTXIMPCONV mkimp sel o diminish c);

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [FORALL_IMPCONV ic Co (!x.A)] returns [(!x.B) ==> (!x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [FORALL_IMPCONV ic Contra (!x.A)] returns [(!x.A) ==> (!x.B)].
 *)
val FORALL_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_FORALL dest_forall;

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [EXISTS_IMPCONV ic Co (?x.A)] returns [(?x.B) ==> (?x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [EXISTS_IMPCONV ic Contra (?x.A)] returns [(?x.A) ==> (?x.B)].
 *)
val EXISTS_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_EXISTS dest_exists;

(* Applies an implicational conversion on the subformula(s) of the input term*)
local val iff_ty = ``:bool->bool->bool`` in
fun SUB_CTXIMPCONV c =
  With_context(
  ((fn v => fn t =>
    let val (n,ty) = dest_const (fst (strip_comb t)) in
    apply
      ((case n of
      "==>" => IMP_CTXIMPCONV
      |"/\\" => CONJ_CTXIMPCONV
      |"\\/" => DISJ_CTXIMPCONV
      |"=" => if ty = iff_ty then IFF_CTXIMPCONV else failwith "SUB_CTXIMPCONV"
      |"!" => FORALL_CTXIMPCONV
      |"?" => EXISTS_CTXIMPCONV
      |"~" => NOT_CTXIMPCONV
      |_ => failwith "SUB_CTXIMPCONV") c)
      v t
    end):imp_conv),
  SUB_CTXIMPCONV o augment c,
  SUB_CTXIMPCONV o diminish c)
end;

(* Takes a theorem which results of an implicational conversion and applies
 * another implicational conversion on the outcome.
 *)
fun bind_ctximpconv (c:imp_conv with_context) v th =
  let val (t1,t2) = dest_imp_only (concl th) in
  case v of
  Co => IMP_TRANS (apply c v t1) th
  |Contra => IMP_TRANS th (apply c v t2)
  end;

fun BIND_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn th => bind_ctximpconv c v th),
    BIND_CTXIMPCONV o augment c,
    BIND_CTXIMPCONV o diminish c));

(* Sequential combinator. *)
fun THEN_CTXIMPCONV (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fn v => fn t => bind_ctximpconv c2 v (apply c1 v t)):imp_conv),
    (fn x => THEN_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fn x => THEN_CTXIMPCONV (diminish c1 x) (diminish c2 x)));

exception Unchanged;

(* Try combinator *)
fun TRY_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      (apply c v t
      handle HOL_ERR _ => ALL_IMPCONV v t)
      handle Unchanged => ALL_IMPCONV v t):imp_conv),
    TRY_CTXIMPCONV o augment c,
    TRY_CTXIMPCONV o diminish c);

(* Applies the first of two implicational conversions that succeeds. *)
fun ORELSE_CTXIMPCONV (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fn v => fn t => apply c1 v t handle HOL_ERR _ => apply c2 v t):imp_conv),
    (fn x => ORELSE_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fn x => ORELSE_CTXIMPCONV (diminish c1 x) (diminish c2 x)));

(* Makes an implicational conversion fail if applying it leaves a term 
 * unchanged.
 *)
fun CHANGED_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t =>
      let 
        val th = apply c v t
        val (l,r) = dest_imp_only (concl th)
      in
        if aconv l r then failwith "CHANGED_CTXIMPCONV" else th
      end):imp_conv),
    CHANGED_CTXIMPCONV o augment c,
    CHANGED_CTXIMPCONV o diminish c);

fun UNCHANGED_OF_FAIL_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fn v => fn t => apply c v t handle HOL_ERR _ => raise Unchanged
      ):imp_conv),
    UNCHANGED_OF_FAIL_CTXIMPCONV o augment c,
    UNCHANGED_OF_FAIL_CTXIMPCONV o diminish c);

local 
  fun map_all f xs x =
    case xs of
    [] => []
    |y::ys => f y x :: map_all f ys x
in
fun REPEAT_UNCHANGED_CTXIMPCONV (cs:imp_conv with_context list) =
  With_context(
    ((fn v => fn t =>
      let
        fun loop changed acc [] =
          if changed then loop false acc cs else acc
        | loop changed acc (c::cs') =
          let val acc' = bind_ctximpconv c v acc in
          loop true acc' cs'
          end
          handle Unchanged => loop changed acc cs'
      in
        loop false (IMP_REFL t) cs
      end):imp_conv),
    REPEAT_UNCHANGED_CTXIMPCONV o map_all augment cs,
    REPEAT_UNCHANGED_CTXIMPCONV o map_all diminish cs)
end;

datatype atomic = Atomic | Non_atomic;

val DEPTH_CTXIMPCONV =
  let
    fun bind c na v th =
      let val (t1,t2) = dest_imp_only (concl th) in
      case v of
      Co => IMP_TRANS (apply c na v t1) th
      |Contra => IMP_TRANS th (apply c na v t2)
      end
    fun self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fn v => fn t =>
        (let val th1 = apply (SUB_CTXIMPCONV (self c)) v t in
          bind c Non_atomic v th1 handle HOL_ERR _ => th1
        end
        handle HOL_ERR e => 
        if #message e = "SUB_CTXIMPCONV" then
          let val th1 = apply c Atomic v t in
            bind_ctximpconv (self c) v th1 handle HOL_ERR _ => th1
          end
        else apply c Non_atomic v t)),
      self o augment c,
      self o diminish c)
  in
    UNCHANGED_OF_FAIL_CTXIMPCONV o self
  end;

local fun self (c:imp_conv with_context) =
  With_context(
    (fn v => fn t =>
      let val th = apply c v t in
        bind_ctximpconv (self c) v th handle HOL_ERR _ => th
      end
      handle HOL_ERR _ => apply (SUB_CTXIMPCONV (self c)) v t),
    self o augment c,
    self o diminish c)
in
val TOP_DEPTH_CTXIMPCONV = UNCHANGED_OF_FAIL_CTXIMPCONV o self
end;

local fun self (c:(atomic->imp_conv) with_context) =
  With_context(
    (fn v => fn t =>
      apply (SUB_CTXIMPCONV (self c)) v t
      handle HOL_ERR e =>
      let
        val a = if #message e = "SUB_CTXIMPCONV" then Atomic else Non_atomic
      in
      apply c a v t
      end),
    self o augment c,
    self o diminish c)
in
val ONCE_DEPTH_CTXIMPCONV = UNCHANGED_OF_FAIL_CTXIMPCONV o self
end;

fun CTXIMPCONV_RULE (c:imp_conv with_context) th =
  MATCH_MP (apply c Contra (concl th)) th;

fun CTXIMPCONV_TAC (cnv:imp_conv with_context) : tactic =
  fn (g as (asms,c)) =>
    let val cnv' = augment cnv asms in
    (MATCH_MP_TAC (apply cnv' Co c) THEN TRY (ACCEPT_TAC TRUTH)) g
    end;

end;

