let rec comparebids (m1:Certified.transaction list) (m2:Certified.transaction list) ((bds:Certified.order list)) sid = match bds with
	|[] -> (Printf.printf "\n############### Comaparison done: Everything looks all right for the stock id: %s on bids side################\n" sid)
	|b::bds' -> if (Certified.qty_bid m1 b.id = Certified.qty_bid m2 b.id) then comparebids m1 m2 bds' sid else 
	  (Printf.printf "\n!!!!!!!!!!!!!!!!Alert: mismatch found in stock id: %s on bid side. Please investigate further!!!!!!!!!!!!!!!!\n" sid)

let rec compareasks (m1:Certified.transaction list) (m2:Certified.transaction list) ((aks:Certified.order list)) sid = match aks with
	|[] -> (Printf.printf "############### Comaparison done: Everything looks all right for the stock id: %s on asks side################\n" sid)
	|a::aks' -> if (Certified.qty_ask m1 a.id = Certified.qty_ask m2 a.id) then compareasks m1 m2 aks' sid else 
	  (Printf.printf "!!!!!!!!!!!!!!!!Alert: mismatch found in stock id: %s on ask side. Please investigate further!!!!!!!!!!!!!!!!\n" sid)



(*Read input data*)
let stocks = (Print.lines_from_files "stocksid")
let datadir = "exchange_inputs_outputs/"
let n = (List.length stocks)

let rec compare stocks= 
match stocks with
	|[] -> Printf.printf "\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@: All comaparisons done for the %d stocks:@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n" n
	|sid::stocks' -> 
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".bid")) 
in let bds = Print.str_list_order_list mylist in
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".ask")) 
in let aks = Print.str_list_order_list mylist in
let mylist = (Print.lines_from_files (datadir ^ sid ^ ".trade")) in
let exchange_matching = Print.str_list_transaction_list mylist in 
comparebids (exchange_matching) (Certified.uM bds aks) bds sid; compareasks (exchange_matching) (Certified.uM bds aks) aks sid; compare stocks'

let () = compare stocks
