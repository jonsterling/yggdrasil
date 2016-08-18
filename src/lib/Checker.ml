open Syntax

let rec spine_infer_check sg sp cods =
  begin
    match (sp, cods) with
    | [], [] ->
      []
    | tm::tms, cod::cods ->
      let lhs =  term_infer_check sg tm  cod  in
      let rhs = spine_infer_check sg tms cods in
      CCList.append lhs rhs
    | _ ->
      assert false
  end

and term_infer_check sg tm cod0 =
  let open Arity in
  match term_infer_infer sg tm with
  | { dom; cod = cod1 } ->
    assert (Term.equal cod0 cod1);
    dom

and term_infer_infer sg tm =
  let open Arity in
  match [@warning "-4"] tm with
  | Term.Ap { op; sp } ->
    let ar = Computad.arity sg op in
    let dom = spine_infer_check sg sp ar.dom in
    { ar with dom }
