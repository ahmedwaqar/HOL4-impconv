(* ========================================================================= *)
(*                                                                           *)
(*                   Implicational rewriting.                                *)
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

structure ImpRewrite =
struct

open HolKernel Parse boolLib ImpConvUtils ImpConv;


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSION                                          *)
(*****************************************************************************)

(* Given a theorem [H1,...,Hn |- P ==> l = r],
 * returns the variables that occur in [P] and [r] but not in the rest.
 * Basically represents the variables that are introduced by the implicational
 * rewrite (similar status as variables occurring in the r.h.s. of a rewrite
 * but not in the l.h.s.).
 *)
fun indep_vars th =
  let 
    val (hs,c) = dest_thm (SPEC_ALL th)
    val (p,c) = dest_imp_only c
    val all_vars = union (free_vars p) (free_vars (rhs c))
    val dep_vars = union (free_vars (lhs c)) (free_varsl hs)
  in
    subtract all_vars dep_vars
  end;

(* Given a list of variables to avoid [v1,...,vk], a theorem of the form
 * [hs |- !x1...xn. p ==> !y1...ym. l = r], and a term [t], matches [t] with
 * [l], yielding the substitution [s], and returns the theorem
 * [s(hs) |- !z1...zp. s(p) ==> s(l) = s(r)] where [z1], ..., [zp] are the
 * variables among [x1], ..., [xn], [y1], ..., [ym] that are not instantiated
 * by [s], and renamed so as to avoid [v1], ..., [vk].
 *)
fun GEN_IMPREWR_CONV avs =
  let 
    val sel = lhs o snd o strip_forall o snd o dest_imp_only
    val pmatch = GEN_PART_MATCH sel
  in
  fn th =>
    let val pmatch' = pmatch th in
    fn t =>
      let val th' = pmatch' t in
        VARIANT_RULE avs (GENL (indep_vars th') th')
      end
    end
  end;

(* A conversion which returns not only a theorem but also a list of terms
 * which is a sublist of the theorem hypotheses, and a list of terms which
 * are the variables newly introduced by the conversion.
 *
 * See [IMPREWR_CONV] for an example.
 *)
type annot_conv = term -> thm * term option * term list;

(* Takes a list of variables to avoid [av], a theorem [th] of the form
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t]
 * and returns a conversion with hypotheses defined as follows:
 * for a term [t], if [t] matches [l] with substitution [s], then return
 * the theorem [h1,...,hk,s(p) |- t = s(r)] and the the list containing only
 * [s(p)].
 *
 * The purpose of the conversion with hypothesis is to be able to distinguish
 * which hypothesis comes from the input theorem and which is added by the
 * conversion itself.
 *)
val IMPREWR_CONV:Tset.t->thm->annot_conv =
  fn avs => fn th =>
    let fun f t = SPEC_VARS (GEN_IMPREWR_CONV avs th t) in
    fn t =>
      let 
        val (vs,uh) = f t
        val u = fst (dest_imp_only (concl uh))
      in
      (UNDISCH uh,SOME u,Tset.of_list vs)
      end
    end;

fun REWR_ANNOTCONV avs th t =
  let 
    val th' = PART_MATCH lhs th t
    val (_,t') = dest_binary_blind (concl th')
    val new_vars = Tset.free_vars t'
    val old_vars = Tset.union (Tset.free_vars t) (Tset.free_varsl (hyp th'))
  in
    (th',NONE,Tset.subtract new_vars old_vars)
  end;

fun ORDER_ANNOTCONV cnv t =
  let 
    val (res as th,_,_) = cnv t
    val (l,r) = dest_binary_blind (concl th)
  in
    case compare (l,r) of
    GREATER => res
    |_ => failwith "ORDER_ANNOTCONV"
  end;

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing 
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
fun pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let 
    val th = SPEC_ALL th
    val lconsts = HOLset.fromList compare (free_varsl (hyp th))
    val t = concl th
    val (f,args) = strip_comb t
    val (n,_) = dest_const f
  in
    case (n,args) of
    ("=",[l,r]) =>
        let val matches = C (can o match_terml [] lconsts) in
        if free_in l r orelse (matches l r andalso matches r l)
        then (t,C REWR_ANNOTCONV (MAP_FORALL_BODY EQT_INTRO th))
        else (l,C REWR_ANNOTCONV th)
        end
    |("==>",[p,c]) =>
        let fun imprewr_concl f = C IMPREWR_CONV (GEN_MAP_CONCLUSION f th) in
        if is_eq c
         then
           let
             val (l,r) = dest_eq c
             val matches = C (can o match_terml [] lconsts)
           in
             if free_in l r orelse (matches l r andalso matches r l) orelse is_var l
             then 
               if matches p c
               then (c, C REWR_ANNOTCONV (EQT_INTRO th))
               else (c, imprewr_concl EQT_INTRO)
             else (l, C IMPREWR_CONV th)
           end
          else if is_neg c then (dest_neg c,imprewr_concl EQF_INTRO)
          else (c, imprewr_concl EQT_INTRO)
        end
    |("~",[l]) => (l, C REWR_ANNOTCONV (EQF_INTRO th))
    |("T",[]) => failwith "pat_cnv_of_thm"
    |_ => (t, C REWR_ANNOTCONV (EQT_INTRO th))
  end;

fun impconv_net_of_thm th =
  let 
    val (p,c) = pat_cnv_of_thm th
    val vs = Tset.free_varsl (hyp th)
  in
    FoNets.enter vs (p,(c,vs,th))
    handle HOL_ERR _ => I
  end;

val patterns_of_thm = fst o pat_cnv_of_thm;

(* Apply a conversion net to the term at the top level, taking
 * avoided variables as parameter too.
 *)
fun REWRITES_IMPCONV
  (net:((term list -> annot_conv) * Tset.t * thm) FoNets.t) avs t =
  tryfind (fn (c,_,_) => c avs t) (FoNets.lookup t net);

local 
  fun REWRITES_CONV rws =
    let val net = net_of rws in 
      fn t => Conv.FIRST_CONV (Net.match t net) t
    end
  fun basic_rewrites () =
    add_rewrites (implicit_rewrites ()) [NOT_FORALL_THM,NOT_IMP]
  fun then1 c1 c2 avs t =
    case c1 avs t of
    c1t as (_,SOME _,_) => c1t
    |c1t as (th1,NONE,vs1) =>
      (let val (th2,ho2,vs2) = c2 (Tset.union vs1 avs) (rand (concl th1)) in
      (TRANS th1 th2, ho2, Tset.union vs1 vs2)
      end
      handle HOL_ERR _ => c1t)
  fun then2 c1 c2 avs t = (then1 c1 c2) avs t handle HOL_ERR _ => c2 avs t
  fun COMB_QCONV c avs l r =
    (case c avs l of
    (th,(ho as SOME _),vs) => (AP_THM th r,ho,vs)
    |(th1,NONE,vs1) =>
      (let val (th2,ho2,vs2) = c (Tset.union vs1 avs) r in
      (MK_COMB (th1,th2), ho2, Tset.union vs1 vs2)
       end
      handle HOL_ERR _ => (AP_THM th1 r,NONE,vs1)))
    handle HOL_ERR _ =>
      let val (th2,ho2,vs2) = c avs r in
      (AP_TERM l th2,ho2,vs2)
      end
  fun SUB_QCONV c avs t =
    case dest_term t of
    COMB(l,r) => COMB_QCONV c avs l r
    |LAMB(v,_) =>
        let 
          val ho = ref NONE
          val vs = ref []
          fun c' t =
            let val (th,ho',vs') = c (Tset.insert avs v) t in
            ho := ho'; vs := vs'; th
            end
          val res = ABS_CONV c' t
        in
          (res,!ho,!vs)
        end
    |_ => failwith "SUB_QCONV"
  fun repeat c avs t = (then1 c (repeat c)) avs t
  fun top_depth c avs t =
    (then2 (repeat c) (then1 (SUB_QCONV (top_depth c)) (top_depth c))) avs t
  fun basic_cnv t = (REWRITES_CONV (basic_rewrites ()) t,NONE,[])
  fun self net ths =
    let 
      val avs = Tset.flat_revmap (Tset.free_varsl o hyp) ths
      fun cnv avs t =
        REWRITES_IMPCONV net avs t handle HOL_ERR _ => basic_cnv t
    in
    With_context(
      (fn a => fn t =>
        let val f = case a of Atomic => top_depth | Non_atomic => I in
        f cnv (Tset.union (Tset.free_vars t) avs) t
        end),
      (fn ts => 
        let
          val ths' = map ASSUME ts
          val ths'' = MP_CLOSURE ths' ths' @ ths' @ MP_CLOSURE ths ths'
        in
        self (itlist impconv_net_of_thm ths'' net) (ths'' @ ths)
        end),
      (fn v =>
        let 
          val ths = ref []
          fun f (_,vs,th) =
            if not (Tset.mem v vs) then (ths := th :: (!ths); true) else false
          val net' = FoNets.filter f net
        in
        self net' (!ths)
        end))
    end
in
val IMPREWR_CTXCONV :thm list -> (atomic->annot_conv) with_context =
  fn ths => self (itlist impconv_net_of_thm ths FoNets.empty_net) ths
end;


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Takes a conversion with hypotheses (with context) and makes an
 * implicational conversion out of it.
 * Basically turns a rewrite with hypotheses into an implicational rewrite
 * withouth hypotheses.
 * Adds existential quantifications for variables introduced by the rewrite.
 *)
local
  val IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`)
  val IMP_EXIST_RULE = CONV_RULE (DEPTH_CONV FORALL_IMP_CONV)
  fun TRY_GEN v th = GEN v th handle HOL_ERR _ => th
in
fun REWR_IMPCONV_OF_CONV (c:(atomic -> annot_conv) with_context) =
  With_context(
    ((fn a => fn v => fn t =>
      let 
        val (th,ho,new_vars) = apply c a t
        val (th1,th2) = EQ_IMP_RULE th
        val res =
          case v of
          Co => 
            let 
              val (p,th2') = UNDISCH_TERM th2
              fun exists_intro [] = DISCH_IMP_IMP (p::list_of_option ho) th2'
                | exists_intro (v::vs) = 
                  let val th = exists_intro vs in
                  IMP_EXIST_RULE (GEN v th) handle HOL_ERR _ => th
                  end
            in
              exists_intro new_vars
            end
          |Contra =>
              let val th1' =
                case ho of NONE => th1 | SOME h => IMP_SYM (DISCH h th1)
              in
                case new_vars of
                [] => th1'
                |_::_ => MAP_CONCLUSION (itlist TRY_GEN new_vars) th1'
              end
        val (t1,t2) = dest_imp_only (concl res)
      in
        if t1 = t2 then raise Unchanged else res
      end):atomic->imp_conv),
    REWR_IMPCONV_OF_CONV o augment c,
    REWR_IMPCONV_OF_CONV o diminish c)
end;

(* Applies the implicational rewrite, with context simplifications. *)
val REWRITE_CTXIMPCONV =
  DEPTH_CTXIMPCONV o REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV;
    

(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* Preprocessor. For now takes a theorem of the form [p ==> c1 /\ ... /\ ck]
 * and returns the list of theorems [p ==> c1], ..., [p ==> ck].
 *)
val preprocess = CONJUNCTS o IMPLY_AND;

(* Tactic for implicational rewrite. *)
fun IMP_REWRITE_TAC ths = 
  CTXIMPCONV_TAC (REWRITE_CTXIMPCONV (flatten (map preprocess ths)));

fun SEQ_IMP_REWRITE_TAC ths =
  let val cnv =
    case ths of
    [] => REWRITE_CTXIMPCONV [TRUTH]
    |[th] => REWRITE_CTXIMPCONV (preprocess th)
    |_::_ =>
        let val fcnv = REWRITE_CTXIMPCONV o preprocess in
        REPEAT_UNCHANGED_CTXIMPCONV (map fcnv ths)
        end
  in
    CTXIMPCONV_TAC cnv
  end;
  
(* Tactic for implicational rewrite with assumptions. *)
fun ASM_IMP_REWRITE_TAC (g as (hs,_)) ths =
  IMP_REWRITE_TAC (map ASSUME hs @ ths) g;

(* Cases-like conversion for implicational theorems, i.e., for a theorem of
 * the form:
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t],
 * return [(p ==> t') /\ (~p ==> t)], where [t'] is the result of rewriting
 * [t] by [l=r].
 *)
local
  val MP_TAUT = MATCH_MP o TAUT
  val MP_LEM1 = MP_TAUT `(~P ==> (Q = R)) ==> (Q <=> (~P ==> R) /\ (P ==> Q))`
  val MP_LEM2 = MP_TAUT `(P ==> (Q = R)) ==> (Q <=> (P ==> R) /\ (~P ==> Q))`
in
fun CASE_REWR_IMPCONV_OF_CONV (c:(atomic -> annot_conv) with_context) =
  With_context(
    (fn a => fn v => fn t =>
      case apply c a t of
      (_,NONE,_) => failwith "CASE_REWR_IMPCONV_OF_CONV"
      |(th,SOME h,_) =>
          let 
            val th' = DISCH h th
            val th'' = MP_LEM1 th' handle HOL_ERR _ => MP_LEM2 th'
          in
            imp_conv_of_conv (REWR_CONV th'') v t
          end),
    CASE_REWR_IMPCONV_OF_CONV o augment c,
    CASE_REWR_IMPCONV_OF_CONV o diminish c)
end;

val CASE_REWRITE_CTXIMPCONV =
  ONCE_DEPTH_CTXIMPCONV o CASE_REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV;

(* Tactic version of it. *)
val CASE_REWRITE_TAC = CTXIMPCONV_TAC o CASE_REWRITE_CTXIMPCONV o preprocess;

end;
