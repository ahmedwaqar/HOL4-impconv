(* ========================================================================= *)
(*                                                                           *)
(*                       Target rewriting.                                   *)
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


structure TargetRewrite =
struct

open HolKernel Parse boolLib ImpConvUtils ImpConv ImpRewrite;


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS WITH MULTIPLE RESULTS                           *)
(*****************************************************************************)

(* Multiple implicational conversion. *)
type imp_mconv = Variance.t -> term -> thm list;

fun mapply_with_context c ctx v t =
  map (DISCH_CONJ ctx) (apply (augment c (Tset.strip_conj ctx)) v t);

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [CONJ_IMPMCONV ic1 ic2 Co (A /\ C)] returns
 * [B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...; Dn
 * ==> A /\ C].
 *
 * And similarly for the contravariant case.
 *)
fun CONJ_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fn v => fn t =>
      let 
        val (t1,t2) = dest_conj t
        val (left,right) =
          case v of
          Co => (MKIMPL_CONJ_CO2_CTXT,MKIMPR_CONJ_CO_CTXT)
          |Contra => (MKIMPL_CONJ_CONTRA_CTXT,MKIMPR_CONJ_CONTRA_CTXT)
        val th1s = map left (mapply_with_context c t2 v t1)
        val th2s = map right (mapply_with_context c t1 v t2)
      in
        th1s @ th2s
      end),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c);

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...; Dn
 * ==> A \/ C].
 *
 * And similarly for the contravariant case.
 *)
fun DISJ_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fn v => fn t =>
      let 
        val (t1,t2) = dest_disj t
        val th1s = map (C MKIMPL_DISJ t2) (apply c v t1)
        val th2s = map (MKIMPR_DISJ t1) (apply c v t2)
      in
        th1s @ th2s
      end),
    DISJ_CTXIMPMCONV o augment c,
    DISJ_CTXIMPMCONV o diminish c);

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C); (A ==> D1) ==> (A
 * ==> C); ...; (A ==> Dn) ==> (A ==> C)].
 *
 * And similarly for the contravariant case.
 *)
fun IMP_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fn v => fn t =>
      let 
        val (t1,t2) = dest_imp_only t
        val th1s = map (C MKIMPL_IMP t2) (apply c (Variance.neg v) t1)
        val th2s = map MKIMPR_IMP_CTXT (mapply_with_context c t1 v t2)
      in
        th1s @ th2s
      end),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c);

fun IFF_CTXIMPCONV (c:imp_mconv with_context) =
  With_context(
    ((fn v => fn t =>
      let 
        val (t1,t2) = dest_iff t
        val (left,right) =
          case v of
          Co => (MKIMPL_CO_IFF,MKIMPR_CO_IFF)
          |Contra => (MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF)
        val th1s = map left (apply c v (mk_imp(t1,t2)))
        val th2s = map right (apply c v (mk_imp(t2,t1)))
      in
        th1s @ th2s
      end):imp_mconv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c);

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * then [NOT_IMPMCONV ic Co ~A] returns [~B1 ==> ~A; ...; ~Bk ==> ~A].
 *
 * And similarly for the contravariant case.
 *)
fun NOT_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fn v => fn t =>
      map MKIMP_NOT (try_list (apply c (Variance.neg v)) (dest_neg t))),
    NOT_CTXIMPMCONV o augment c,
    NOT_CTXIMPMCONV o diminish c);

fun QUANT_CTXIMPMCONV mkimp sel (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fn v => fn t =>
      let 
        val (x,b) = sel t
        val c' = diminish c x
      in
        map (mkimp x) (try_list (apply c' v) b)
      end),
    QUANT_CTXIMPMCONV mkimp sel o augment c,
    QUANT_CTXIMPMCONV mkimp sel o diminish c);

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [FORALL_IMPMCONV ic Co (!x.A)] returns [(!x.B1) ==> (!x.A); ...;
 * (!x.Bk) ==> (!x.A)].
 *
 * And similarly for the contravariant case.
 *)
val FORALL_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_FORALL dest_forall;

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [EXISTS_IMPMCONV ic Co (?x.A)] returns [(?x.B1) ==> (?x.A); ...;
 * (?x.Bk) ==> (?x.A)].
 *
 * And similarly for the contravariant case.
 *)
val EXISTS_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_EXISTS dest_exists;

(* Applies a multiple implicational conversion on the subformula(s) of the
 * input term
 *)
local val iff_ty = ``:bool->bool->bool`` in
fun SUB_CTXIMPMCONV c =
  With_context(
    ((fn v => fn t =>
      let val (n,ty) = dest_const (fst (strip_comb t)) in
      apply
        ((case n of
        "==>" => IMP_CTXIMPMCONV
        |"/\\" => CONJ_CTXIMPMCONV
        |"\\/" => DISJ_CTXIMPMCONV
        |"!" => FORALL_CTXIMPMCONV
        |"?" => EXISTS_CTXIMPMCONV
        |"~" => NOT_CTXIMPMCONV
        |"=" =>
            if ty = iff_ty then IFF_CTXIMPCONV else failwith "SUB_CTXIMPMCONV"
        |_ => failwith "SUB_CTXIMPMCONV") c) v t
      end):imp_mconv),
    SUB_CTXIMPMCONV o augment c,
    SUB_CTXIMPMCONV o diminish c)
end;


(* Applies a multiple implicational conversion once to the first suitable sub-term(s)
 * encountered in bottom-up order.
 *)
fun DEPTH_CTXIMPMCONV (c : (atomic->imp_mconv) with_context) =
  With_context(
    (fn v => fn t =>
      let val ths = apply (SUB_CTXIMPMCONV (DEPTH_CTXIMPMCONV c)) v t in
      apply c Non_atomic v t @ ths
      end
      handle HOL_ERR e =>
        if #message e = "SUB_CTXIMPMCONV" then apply c Atomic v t
        else raise HOL_ERR e),
      DEPTH_CTXIMPMCONV o augment c,
      DEPTH_CTXIMPMCONV o diminish c);


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

(* Multiple implicational conversion with hypotheses. *)
type annot_mconv = term -> (thm * term option * term list) list;

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
fun target_pat_cnv_of_thm th : (term * (term list -> annot_conv)) =
  let 
    val th = SPEC_ALL th
    val t = concl th
    val (f,args) = strip_comb t
    val (n,_) = dest_const f
  in
    case (n,args) of
    ("=",[l,_]) => (l,C REWR_ANNOTCONV th)
    |("==>",[_,c]) =>
      let 
        val (f,args) = strip_comb c
        val (n,_) = dest_const f
        val (pat,th') =
          case (n,args) of
          ("=",[l,_]) => (l,th)
          |("~",[l]) => (l, GEN_MAP_CONCLUSION EQF_INTRO th)
          |_ => (c, GEN_MAP_CONCLUSION EQT_INTRO th)
      in
        (pat, C IMPREWR_CONV th')
      end
    |("~",[l]) => (l, C REWR_ANNOTCONV (EQF_INTRO th))
    |("T",[]) => failwith "target_pat_cnv_of_thm"
    |_ => (t, C REWR_ANNOTCONV (EQT_INTRO th))
  end;

fun target_impconv_net_of_thm th =
  let 
    val (p,c) = target_pat_cnv_of_thm th
    val vs = Tset.free_varsl (hyp th)
  in
    FoNets.enter vs (p,(c,vs,th))
  end
  handle HOL_ERR _ => I;

val target_patterns_of_thm = fst o target_pat_cnv_of_thm;

(* Multiple conversion which returns all the possible rewrites (on one subterm
 * only) by one theorem.
 *)

val DEEP_IMP_REWR_MCONV:thm list->(atomic->annot_mconv) with_context =
  let 
    fun map_fst f (x,y,z) = (f x,y,z)
    fun COMB_MCONV c l r =
      map (map_fst (C AP_THM r)) (c l) @ map (map_fst (AP_TERM l)) (c r)
    fun ABS_MCONV c v b =
      let val ths = c b in
      map (map_fst (ABS v)) ths
      handle HOL_ERR _ =>
        let 
          val gv = genvar (type_of v)
          fun f (gth,ho,vs) =
            let 
              val gtm = concl gth
              val (l,r) = dest_eq gtm
              val v' = variant (free_vars gtm) v
              val l' = alpha_ v' l
              val r' = alpha_ v' r
            in
              (EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth,ho,vs)
            end
          val b' = subst[v|->gv] b
        in
          map f (map (map_fst (ABS gv)) (c b'))
        end
      end
    fun SUB_MCONV c t =
      case dest_term t of
      COMB(l,r) => COMB_MCONV c l r
      |LAMB(v,b) => ABS_MCONV c v b
      |CONST _ => []
      |VAR _ => []
    fun top_depth c t = SUB_MCONV (top_depth c) t @ c t
    fun REWRITES_IMPCONV 
      (net:((term list -> annot_conv) * Tset.t * thm) FoNets.t) avs t =
      mapfilter (fn (c,_,_) => c avs t) (FoNets.lookup t net)
    fun self net ths =
      let val avs = Tset.flat_revmap (Tset.free_varsl o hyp) ths in
      With_context(
        (fn a => fn t =>
          let 
            val avs' = Tset.union (Tset.free_vars t) avs
            fun cnv t = REWRITES_IMPCONV net avs' t
            val f =
              case a of
                Atomic => top_depth
                |Non_atomic => (fn c => fn avs => c avs)
          in
            f cnv t
          end),
        (fn _ => self net ths),
        (fn v =>
          let 
            val ths = ref []
            fun f (_,vs,th) =
              if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
            val net' = FoNets.filter f net
          in
            self net' (!ths)
          end))
      end
  in
  fn ths =>
    self (itlist target_impconv_net_of_thm ths FoNets.empty_net) ths
  end;

(* Takes a multiple conversion with hypotheses (which also takes a context as
 * parameter) and makes a multiple implicational conversion out of it.
 *
 * Basically extends [GENERAL_REWRITE_IMPCONV] to the multiple conversion
 * case.
 *)
local
  val IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`)
  val IMP_EXIST_RULE = CONV_RULE (DEPTH_CONV FORALL_IMP_CONV)
  fun TRY_GEN v th = GEN v th handle HOL_ERR _ => th
in
fun REWR_IMPMCONV_OF_MCONV (c:(atomic -> annot_mconv) with_context) =
  With_context(
    ((fn a => fn v => fn t =>
      let fun f (th,ho,new_vars) =
        let val (th1,th2) = EQ_IMP_RULE th in
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
        end
      in
        map f (apply c a t)
      end):atomic->imp_mconv),
      REWR_IMPMCONV_OF_MCONV o augment c,
      REWR_IMPMCONV_OF_MCONV o diminish c)
end;


(*****************************************************************************)
(* TARGET REWRITING                                                          *)
(*****************************************************************************)

val EXISTS_CTXIMPCONV:imp_conv with_context =
  let 
    fun EXISTSs i p =
      let 
        val (dom,codom) = unzip (map (fn x => (#redex x,#residue x)) i)
        fun f i ps = subst [i] (snd (dest_exists (hd ps))) :: ps
        val (h,ps) =
          case rev_itlist f i [list_mk_exists(dom,p)] of
          [] => failwith "EXISTSs"
          |h::ps => (h,ps)
      in
        rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h)
      end
    val FORALL_IMP_RULE = CONV_RULE (DEPTH_CONV FORALL_IMP_CONV)
    fun self ts =
      With_context
        ((fn v => fn t =>
          case (v,is_exists t) of
          (Co,true) =>
              let 
                val (vs,b) = strip_exists t
                val bs = strip_conj b
                fun hmatch (n,b) =
                  case partition (C mem vs) (all_vars b) of
                  ([],_) => failwith "EXISTS_CTXIMPCONV"
                  |((lvs as (_::_)),lcs) =>
                      fn h =>
                        let
                          val (i,j) =
                            match_terml [] (HOLset.fromList compare lcs) b h
                        in
                          if filter (fn x => #redex x <> #residue x) j = [] 
                          then
                            ((if i = [] then map (fn x => x|->x) lvs else i),n)
                          else failwith "EXISTS_CTXIMPCONV"
                        end
                val (s,n) =
                  tryfind_fun (mapfilteri (curry (tryfind o hmatch)) bs) ts
                val th = EXISTSs (map (fn v => v |-> subst_assocd v s v) vs) b
                val th' = DISCH_HD th
                val h = fst (dest_imp_only (concl th'))
              in
              (case strip_conj h of
              [] => failwith "EXISTS_CTXIMPCONV"
              |[h] => DISCH T_ th
              |hs as (_::_) =>
                let
                  val (hs1,hs2') = split_after n hs
                  val (h',hs2) =
                    case hs2' of
                    [] => failwith "EXISTS_CTXIMPCONV" 
                    |h'::hs2 => (h',hs2)
                  val hs_th = CONJUNCTS_AC (h,list_mk_conj (h'::(hs1@hs2)))
                  val th1 = CONV_RULE (LAND_CONV (REWR_CONV hs_th)) th'
                  val th2 = UNDISCH (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) th1)
                  val vs' = subtract vs (map #redex s)
                  fun f v th = FORALL_IMP_RULE (GEN v th) handle HOL_ERR _ => th
                in
                  itlist f vs' th2
                end)
              end
          |_ => failwith "EXISTS_CTXIMPCONV"),
          (fn ts' => self (Tset.union ts' ts)),
          (fn _ => self ts))
  in
    self []
  end;

(* Takes a theorem which results of an implicational conversion and applies a
 * multiple implicational conversion on the outcome.
 *)
fun bind_impmconv (c:imp_mconv) v th =
  let val (t1,t2) = dest_imp_only (concl th) in
  case v of
  Co => map (C IMP_TRANS th) (c v t1)
  |Contra => map (IMP_TRANS th) (c v t2)
  end;


(* Target rewrite implicational conversion:
 * [TARGET_REWRITE_IMPCONV sths ts] is an implicational conversion which
 * applies all the possible implicational rewrites on the input term until
 * one of the resulting terms matches one of the terms in [ts].
 *
 * Note that we allow several target terms and not just one. See 
 * TARGET_REWRITE_TAC for a justification.
 *)
val TARGET_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  let 
    val PRE = apply (TRY_CTXIMPCONV (REWRITE_CTXIMPCONV []))
    val POST = TRY_CTXIMPCONV (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV)
  in
  fn sths =>
    let
      fun one_step_sths v uh =
        let 
          fun pre v th = bind_impconv PRE v th handle Unchanged => th
          fun post v = bind_ctximpconv POST v
          val f =
            DEPTH_CTXIMPMCONV o REWR_IMPMCONV_OF_MCONV o DEEP_IMP_REWR_MCONV
        in
          map (post v) (bind_impmconv (apply (f sths)) v (pre v uh))
        end
      fun flat l =
        itlist (C (curry HOLset.addList)) l (HOLset.empty (uncurry thm_compare))
    in
      fn ts => fn v => fn t =>
        let fun self ths =
          let
            val pool = flat (map (one_step_sths v) ths)
            fun sel th = imp_conv_outcome th v
            fun is_one_sol g = (can o find_term o can o match_term) g o sel
            fun is_sol th = tryfind is_one_sol ts th
          in
            case HOLset.find is_sol pool of
            SOME sol => bind_ctximpconv POST v sol
            |NONE =>
              (if HOLset.isEmpty pool
              then failwith "TARGET_REWRITE_IMPCONV: no path found"
              else self (map (bind_ctximpconv POST v) (HOLset.listItems pool)))
          end
        in
          self [IMP_REFL t]
        end
    end
  end;

(* Tactic version of it.
 *
 * Since the target theorem is preprocessed, it can yield several theorems.
 * Therefore, there is not just one possible target pattern but several.
 *)
fun TARGET_REWRITE_TAC sths th =
  let 
    val sths' = flatten (map preprocess sths)
    val ths = preprocess th
  in
    IMPCONV_TAC
    (THEN_IMPCONV (TARGET_REWRITE_IMPCONV sths' (map patterns_of_thm ths))
      (imp_conv_of_ctx_imp_conv (REWRITE_CTXIMPCONV ths)))
  end;

val HINT_EXISTS_TAC = CTXIMPCONV_TAC (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV);

end;
