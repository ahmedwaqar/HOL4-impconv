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

structure ImpConvUtils =
struct

  open HolKernel Parse boolLib tautLib bossLib;

  (* Same as [UNDISCH] but also returns the undischarged term *)
  fun UNDISCH_TERM th = (fst (dest_imp_only (concl th)), UNDISCH th);

  (* Same as [UNDISCH_ALL] but also returns the undischarged terms *)
  fun UNDISCH_TERMS th =
    let
      val (t,th') = UNDISCH_TERM th
      val (ts,th'') = UNDISCH_TERMS th'
    in
      (t::ts,th'')
    end
    handle HOL_ERR _ => ([],th);

  (* Comblies the function [f] to the conclusion of an implicational theorem. *)
  fun MAP_CONCLUSION f th =
    let val (p,th) = UNDISCH_TERM th in
      DISCH p (f th)
    end;

  (* For a list [f1;...;fk], returns the first [fi x] that succeeds. *)
  fun tryfind_fun fs x =
    case fs
    of [] => failwith "tryfind_fun"
    |f::fs' => (f x handle HOL_ERR _ => tryfind_fun fs' x);

  fun subst_assocd y ys x =
     let
        fun assc [] = x
          | assc ({redex, residue} :: rst) =
              if redex = y then residue else assc rst
     in
        assc ys
     end;

  (* Same as [mapfilter] but also provides the rank of the iteration as an 
   * argument to [f]. *)
  fun mapfilteri f =
    let 
      fun self _ [] = []
        | self i (h::t) =
          let val rest = self (i+1) t in
            f i h :: rest
            handle HOL_ERR _ => rest
          end
    in
      self 0
    end;

  fun list_of_option NONE = []
    | list_of_option (SOME x) = [x];

  fun try_list f x = f x handle HOL_ERR _ => [];

  (* A few constants. *)
  val A_ = ``A:bool`` and B_ = ``B:bool``;
  val C_ = ``C:bool`` and D_ = ``D:bool``;
  val T_ = ``T:bool``;
  val bool_ty = ``:bool``;
  val aty = ``:'a``;
  fun mk_fun_ty a b = mk_type("fun",[a,b]);

  fun dest_iff t =
    let val (l,r) = dest_eq t in
      if type_of l = bool_ty then (l,r) else failwith "dest_iff"
    end;

  val MONO_FORALL =
    METIS_PROVE [] ``(!x. P x ==> Q x) ==> (!x. P x) ==> (!x. Q x)``;

  (* For a term t, builds ``t ==> t`` *)
  val IMP_REFL =
    let val lem = TAUT `A ==> A` in
    fn t => INST [A_ |-> t] lem end;

  fun alpha_ v tm =
    let val (v0,bod) =
      dest_abs tm handle HOL_ERR _ => failwith "alpha: Not an abstraction"
    in
      if v = v0 then tm else
      if type_of v = type_of v0 andalso not (free_in v bod) then
        mk_abs (v, subst [v0 |-> v] bod)
      else failwith "alpha: Invalid new variable"
    end;

  fun variants av [] = []
    | variants av (h::t) =
      let val vh = variant av h in vh::(variants (vh::av) t) end;

  (* Conversion version of [variant]:
   * Given variables [v1;...;vk] to avoid and a term [t],
   * returns [|- t = t'] where [t'] is the same as [t] without any use of the
   * variables [v1;...;vk].
   *)
  fun VARIANT_CONV av t =
    let 
      val vs = free_vars t
      val mapping = filter (fn (x,y) => x <> y) (zip vs (variants av vs))
    in
      DEPTH_CONV (fn u => ALPHA_CONV (assoc (bvar u) mapping) u) t
    end;

  (* Rule version of [VARIANT_CONV] *)
  val VARIANT_RULE = CONV_RULE o VARIANT_CONV;

  fun GEN_PART_MATCH partfn th =
    let
      val th = SPEC_ALL th
      val bod = concl th
      val conclfvs = Term.FVL [bod] empty_tmset
      val hypfvs = Thm.hyp_frees th
      val hyptyvars = HOLset.listItems (Thm.hyp_tyvars th)
      val pbod = partfn bod
      val lconsts = HOLset.intersection (conclfvs, hypfvs)
      val matchfn = match_terml hyptyvars lconsts pbod
      val fvs = subtract (subtract (free_vars bod) (free_vars pbod))
        (HOLset.listItems lconsts)
      val th' = GENL fvs th
      fun spec _ th = snd (SPEC_VAR th)
     in
       fn tm => itlist spec fvs (INST_TY_TERM (matchfn tm) th')
     end;

  (* Discharges the first hypothesis of a theorem. *)
  fun DISCH_HD th = DISCH (hd (hyp th)) th;

  (* Rule version of [REWR_CONV] *)
  val REWR_RULE = CONV_RULE o REWR_CONV;

  (* Given a list [A1;...;Ak] and a theorem [th],
   * returns [|- A1 /\ ... /\ Ak ==> th].
   *)
  val DISCH_IMP_IMP =
    let 
      fun f [] = I
        | f (t::ts) =
          rev_itlist (fn t => REWR_RULE AND_IMP_INTRO o DISCH t) ts o DISCH t
    in
      f o rev
    end;

  fun print_endline s = print (s ^ "\n");
  fun thm_to_string th =
    let val (hs,c) = dest_thm th in
    concat (map (fn h => term_to_string h ^ ", ") hs) ^ " |- " ^ term_to_string c
    end;

  (* Given a term [A /\ B] and a theorem [th], returns [|- A ==> B ==> th]. *)
  fun DISCH_CONJ t th =
    let val (t1,t2) = dest_conj t in
    REWR_RULE AND_IMP_INTRO (DISCH_CONJ t1 (DISCH_CONJ t2 th))
    end
    handle HOL_ERR _ => DISCH t th;

  (* Specializes all the universally quantified variables of a theorem,
   * and returns both the theorem and the list of variables.
   *)
  fun SPEC_VARS th =
    let 
      val (v,th') = SPEC_VAR th
      val (vs,th'') = SPEC_VARS th'
    in
      (v::vs,th'')
    end
    handle HOL_ERR _ => ([],th);

  (* Comblies the function [f] to the body of a universally quantified theorem. *)
  fun MAP_FORALL_BODY f th =
    let val (vs,th) = SPEC_VARS th in GENL vs (f th) end;

  (* Given a theorem of the form [!xyz. P ==> !uvw. C] and a function [f],
   * return [!xyz. P ==> !uvw. f C].
   *)
  val GEN_MAP_CONCLUSION = MAP_FORALL_BODY o MAP_CONCLUSION o MAP_FORALL_BODY;

  (* Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].
   * Also deals with universal quantifications if necessary
   * (e.g., [x ==> !v. y /\ z] will be turned into
   * [(x ==> !v. y) /\ (x ==> !v. z)])
   *
   * possible improvement: apply the rewrite more locally
   *)
  val IMPLY_AND =
    let
      val IMPLY_AND_RDISTRIB =
        TAUT `(x ==> y /\ z) <=> (x==>y) /\ (x==>z)`
    in
      CONV_RULE (REPEATC (DEPTH_CONV (FIRST_CONV [
        FORALL_AND_CONV,REWR_CONV AND_IMP_INTRO,
        RIGHT_IMP_FORALL_CONV,REWR_CONV IMPLY_AND_RDISTRIB,
        REWR_CONV CONJ_ASSOC])))
    end;

  (* Returns the two operands of a binary combination.
   * Contrary to [dest_binary], does not check what is the operator.
   *)
  fun dest_binary_blind t =
    case strip_comb t of
    (_,[l,r]) => (l,r)
    |_ => failwith "dest_binary_blind";

  val spec_all = repeat (snd o dest_forall);

  fun thm_compare th1 th2 =
    list_compare compare ((concl th1::hyp th1),(concl th2::hyp th2));

  fun thm_lt th1 th2 = thm_compare th1 th2 = LESS;

  fun equals_thm th1 th2 = thm_compare th1 th2 = EQUAL;

  (* GMATCH_MP (U1 |- !x1...xn. H1 /\ ... /\ Hk ==> C) (U2 |- P)
   * = (U1 u U2 |- !y1...ym. G1' /\ ... /\ Gl' ==> C')
   * where:
   * - P matches some Hi
   * - C' is the result of applying the matching substitution to C
   * - Gj' is the result of applying the matching substitution to Hj
   * - G1',...,Gl' is the list corresponding to H1,...,Hk but without Hi
   * - y1...ym are the variables among x1,...,xn that are not instantiated
   *
   * possible improvement: make a specific conversion,
   * define a MATCH_MP that also returns the instantiated variables *)
  val GMATCH_MP =
    let
      val swap = CONV_RULE (REWR_CONV (TAUT `(p==>q==>r) = (q==>p==>r)`))
      val AND_IMP = GSYM AND_IMP_INTRO
    in
    fn th1 =>
      let 
        val (vs,th1') = SPEC_VARS th1
        val (hs,th1'') = UNDISCH_TERMS (PURE_REWRITE_RULE [AND_IMP] th1')
      in
      fn th2 =>
        let
          fun f h hs =
            let
              val th1''' = DISCH h th1''
              val th1'''' =
                swap (DISCH_IMP_IMP hs th1''') handle HOL_ERR _ => th1'''
            in
              MATCH_MP (GENL vs th1'''') th2
            end
          fun loop _ [] = []
            | loop acc (h::hs) =
                ([f h (acc @ hs)] handle HOL_ERR _ => []) @ loop (h::acc) hs
        in
          loop [] hs
        end
      end
    end;

  fun GMATCH_MPS ths1 ths2 =
    let 
      fun insert (y:thm) [] = [y]
        | insert y (x::xs) =
          if equals_thm x y then (x::xs)
          else if thm_lt x y then x :: insert y xs
          else y::x::xs
      fun inserts ys = itlist insert ys
    in
    case ths1 of
    [] => []
    |th1::ths1' =>
      let 
        fun self acc th1 ths1 [] =
          (case ths1 of [] => acc | th::ths1' => self acc th ths1' ths2)
        | self acc th1 ths1 (th2::ths2') =
          self (inserts (GMATCH_MP th1 th2) acc) th1 ths1 ths2' 
      in
        self [] th1 ths1' ths2
      end
    end;

  fun MP_CLOSURE ths1 ths2 =
    let
      val ths1 = filter (is_imp o spec_all o concl) ths1
      fun self ths2 [] = []
      | self ths2 (ths1' as (th::ths1)) =
        let val ths1'' = GMATCH_MPS ths1' ths2 in
          self ths2 ths1'' @ ths1''
        end
    in
      self ths2 ths1
    end;

  (* Set of terms. Implemented as ordered lists. *)
  structure Tset =
    struct
      type t = term list
      fun lt (x:term) y = compare (x,y) = LESS
      fun lift f = sort lt o f
      val of_list = lift I
      fun insert ts t =
        let
          fun self [] = [t]
          | self (x::xs) =
            case compare (x,t) of
            LESS => x::self xs
            |EQUAL => x::xs
            |GREATER => t::x::xs
        in
          if t = T_ then ts else self ts
        end
      fun remove ts t =
        let 
          fun self [] = []
          |self (x::xs) =
            case compare (x,t) of
            LESS => x::self xs
            |EQUAL => xs
            |GREATER => x::xs
        in
          self ts
        end
      val strip_conj =
        let
          fun self acc t =
            let val (t1,t2) = dest_conj t in
              self (self acc t1) t2
            end
            handle HOL_ERR _ => insert acc t
        in
          self []
        end
      fun union [] l2 = l2
        | union l1 [] = l1
        | union (h1::t1) (h2::t2) =
          case compare (h1,h2) of
          LESS => h1::union t1 (h2::t2)
          |EQUAL => h1::union t1 t2
          |GREATER => h2::union (h1::t1) t2
      fun mem x [] = false
        | mem x (y::ys) =
          case compare (y,x) of
          LESS => mem x ys
          |EQUAL => true
          |GREATER => false
      fun subtract l1 l2 = filter (fn x => not (mem x l2)) l1
      val empty = []
      fun flat_revmap f =
        let
          fun self acc [] = acc
            | self acc (x::xs) = self (union (f x) acc) xs
        in
          self []
        end
      fun flat_map f = flat_revmap f o rev
      val free_vars = lift free_vars
      val free_varsl = lift free_varsl
    end;
end;
