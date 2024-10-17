open Str
(**Read data from a file**)
let read_line ic = try Some (input_line ic) with End_of_file -> None 
let lines_from_files filename = 
  let rec lines_from_files_aux ic acc = match (read_line ic) with 
    | None -> acc              (*To output in the same order, please do List.rev acc *)
    | Some s -> lines_from_files_aux ic (s :: acc) in 
  lines_from_files_aux (open_in filename) [] 

(**Functions to read bids and asks (order) data from the file**)

(*type order = { id : int; otime : int; oquantity : int; oprice : int }*)
let createorder l:Certified.order=
	match l with 
		|[i;t;p;q] -> {Certified.id=i;Certified.otime=t;Certified.oquantity=q;Certified.oprice=p}  
		|_ ->raise (Invalid_argument "Order information is incomplete");;

let string_to_order line=createorder (List.map int_of_string (String.split_on_char ',' line));;

(*This function takes a list of strings and converts them into list of order records*)
let rec str_list_order_list mylist = match mylist with
	| [] ->[]
	| line::mylist' ->(string_to_order line)::(str_list_order_list mylist')


(** These functions read data from files and convert them into list of transactions **)
(* Convert list of four tuples into a transaction*)
let createtransaction l =
	match l with 
		|[i1;i2;p;q] -> {Certified.idb=i1;Certified.ida= i2;Certified.tprice=p;Certified.tquantity=q}  
		|_ ->raise (Invalid_argument "Trade information is incomplete");;

(* Split a string by commas and then convert each value into a number and them output into transaction *)
let string_to_transaction line = createtransaction (List.map int_of_string (String.split_on_char ',' line));;

(* Take a list of strings and convert them into list of transactions *)
let rec str_list_transaction_list mylist= match mylist with
	| [] ->[]
	| line::mylist' ->(string_to_transaction line)::(str_list_transaction_list mylist')


(**Functions write trades data in a file**)
let rec printm (m:Certified.transaction list) sid = match m with
	|[] -> (Printf.printf "#################### End of Trades for stock %s ####################\n\n" sid)
	|f::m' -> (Printf.printf "Buy id: %i, Sell id: %i, Price: %i, Quantity: %i\n" f.Certified.idb f.Certified.ida f.Certified.tprice f.Certified.tquantity);printm m' sid

let rec printmfile oc = function 
  | [] -> ()
  | f::m -> Printf.fprintf oc "%d,%d,%d,%d\n" f.Certified.idb f.Certified.ida f.Certified.tprice f.Certified.tquantity; printmfile oc m

let writematching file (m:Certified.transaction list) =
  let oc = open_out file in
  printmfile oc m;
  close_out oc;
  
