module E = Expression


type status_t =
  Unverified      |   (* The formula has not been analyzed              *)
  Invalid         |   (* The formula is invalid                         *)
  Valid of DP.t       (* The formula is valid                           *)


type info_t =
  {
    status : status_t;
    time : float;
  }


(******************)
(*  CONSTRUCTORS  *)
(******************)

let new_info (status:status_t) (time:float) : info_t =
  {
    status = status;
    time = time;
  }


let status_to_str (st:status_t) : string =
  match st with
  | Unverified -> "Unverified"
  | Invalid    -> "Invalid"
  | Valid dp   -> "Valid (" ^DP.to_str dp^ ")"


let get_status (info:info_t) : status_t =
  info.status


let get_time (info:info_t) : float =
  info.time



