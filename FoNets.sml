(* ========================================================================= *)
(*                                                                           *)
(*           First-order matching and nets.                                  *)
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
(* HOL4 already has several implementations of net, it seemed to me easier   *)
(* to just port my HOL Light version rather than investigating deeply which  *)
(* HOL4 one was good for my needs...                                         *)
(* Basically, these nets have the two following features:                    *)
(* - first-order (like HOL4 Nets, but if I understood well not like Ho_nets) *)
(*   Note that this is on purpose: higher-order implicational rewriting      *)
(*   generally rewrites too much...                                          *)
(* - given a theorem [x=0] |- x = 0, does not match x with anything else     *)
(*   x (like Ho_nets, but unlike Nets, if I understood well).                *)
(*                                                                           *)
(* ========================================================================= *)

structure FoNets =
struct

open HolKernel Parse boolLib bossLib;

datatype term_label =
  Vnet of int
  |Lcnet of string * int
  |Cnet of string * int
  |Lnet of int

datatype 'a t = Netnode of (term_label * 'a t) list * 'a list

fun exists_subterm p t =
  (ignore (find_term p t);true) handle HOL_ERR _ => false;

val empty_net = Netnode([],[])

fun label_to_store lcs t =
  let 
    val (opr,args) = strip_comb t
    val nargs = length args
  in
    case dest_term opr of
    CONST{Name = n,...} => (Cnet(n,nargs),args)
    |LAMB(v,b) =>
       let val b' = if mem v lcs then subst [v|->genvar(type_of v)] b else b in
       (Lnet nargs,b'::args)
       end
    |VAR(n,_) =>
        if mem opr lcs then (Lcnet(n,nargs),args) else (Vnet nargs,args)
    |_ => fail()
  end

fun net_update _ elem (Netnode(edges,tips)) [] =
   Netnode(edges,elem::tips)
  | net_update lcs elem (Netnode(edges,tips)) (t::rts) =
      let 
        val (label,nts) = label_to_store lcs t
        val (child,others) =
          let val ((_,n),edges') = (pluck (fn (x,y) => x = label) edges) in
            (n,edges')
          end
          handle HOL_ERR _ => (empty_net,edges)
        val new_child = net_update lcs elem child (nts@rts)
      in
        Netnode ((label,new_child)::others,tips)
      end

fun enter lcs (t,elem) net = net_update lcs elem net [t]

fun label_for_lookup t =
  let
    val (opr,args) = strip_comb t
    val nargs = length args
  in
    case dest_term opr of
    CONST{Name = n,...} => (Cnet(n,nargs),args)
    |LAMB(_,b) => (Lnet nargs,b::args)
    |VAR(n,_) => (Lcnet(n,nargs),args)
    |COMB _ => fail()
  end

fun follow (Netnode(_,tips)) [] = tips
  | follow (Netnode(edges,tips)) (t::rts) =
      let
        val (label,nts) = label_for_lookup t
        val collection =
          follow (assoc label edges) (nts@rts) handle HOL_ERR _ => []
          (* HERE is the major difference: *)
        fun support [] = [(0,rts)]
          | support (t::ts) =
            (case support ts of
            res as ((k,nts')::res') => (k+1,(t::nts'))::res
            |[] => fail ())
        fun f (k,nts) =
          follow (assoc (Vnet k) edges) nts handle HOL_ERR _ => []
        val follows = map f (support nts)
      in
        collection @ flatten follows
      end;

fun lookup t net = follow net [t]

fun filter p (Netnode(edges,tips)) =
  Netnode(map (fn (l,n) => (l,filter p n)) edges, List.filter p tips)
end;
