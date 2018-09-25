Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import hmacdrbg.entropy.
Require Import VST.floyd.functional_base.

Definition DRBG_working_state: Type := (list byte * list byte * Z)%type. (* value * key * reseed_counter *)
Definition DRBG_state_handle: Type := (DRBG_working_state * Z * bool)%type. (* state, security_strength, prediction_resistance_flag *)

Definition DRBG_instantiate_function
            (instantiate_algorithm: list byte -> list byte -> list byte -> Z -> DRBG_working_state)
            (min_entropy_length max_entropy_length: Z) (provided_nonce: option (list byte))
            (highest_supported_security_strength: Z) (max_personalization_string_length: Z)
            (prediction_resistance_supported: bool) (entropy_stream: ENTROPY.stream)
            (requested_instantiation_security_strength: Z) (prediction_resistance_flag: bool)
            (personalization_string: list byte): ENTROPY.result DRBG_state_handle :=
  if requested_instantiation_security_strength >? highest_supported_security_strength then ENTROPY.error ENTROPY.generic_error entropy_stream
  else match prediction_resistance_flag, prediction_resistance_supported with
         | true, false => ENTROPY.error ENTROPY.generic_error entropy_stream
         | _,_ =>
           if (Zlength personalization_string) >? max_personalization_string_length then ENTROPY.error ENTROPY.generic_error entropy_stream
           else
             let security_strength := if requested_instantiation_security_strength <=? 14 then Some 14
                                      else if requested_instantiation_security_strength <=? 16 then Some 16
                                      else if requested_instantiation_security_strength <=? 24 then Some 24
                                      else if requested_instantiation_security_strength <=? 32 then Some 32
                                      else None in
             match security_strength with
               | None => ENTROPY.error ENTROPY.generic_error entropy_stream
               | Some security_strength =>
               match get_entropy security_strength min_entropy_length max_entropy_length prediction_resistance_flag entropy_stream with
                 | ENTROPY.error e s' => ENTROPY.error ENTROPY.catastrophic_error s'
                 | ENTROPY.success entropy_input entropy_stream =>
                   let nonce_result := match provided_nonce with
                                         | Some n => ENTROPY.success n entropy_stream
                                         | None => get_entropy (security_strength/2) (min_entropy_length/2) (max_entropy_length/2)
                                                               prediction_resistance_flag entropy_stream
                                       end in
                   match nonce_result with
                     | ENTROPY.error e s' => ENTROPY.error ENTROPY.catastrophic_error s'
                     | ENTROPY.success nonce entropy_stream =>
                       let initial_working_state := instantiate_algorithm entropy_input nonce personalization_string security_strength in
                       ENTROPY.success (initial_working_state, security_strength, prediction_resistance_flag) entropy_stream
                   end
               end
             end
       end.

Definition DRBG_reseed_function (reseed_algorithm: DRBG_working_state -> list byte -> list byte -> DRBG_working_state)
            (min_entropy_length max_entropy_length: Z) (max_additional_input_length: Z)
            (entropy_stream: ENTROPY.stream) (state_handle: DRBG_state_handle)
            (prediction_resistance_request: bool) (additional_input: list byte): ENTROPY.result DRBG_state_handle :=
  match state_handle with (working_state, security_strength, prediction_resistance_flag) =>
  if prediction_resistance_request && (negb prediction_resistance_flag) then ENTROPY.error ENTROPY.generic_error entropy_stream
  else
    if Zlength additional_input >? max_additional_input_length then ENTROPY.error ENTROPY.generic_error entropy_stream
    else
      match get_entropy security_strength min_entropy_length max_entropy_length prediction_resistance_request entropy_stream with
        | ENTROPY.error _ s => ENTROPY.error ENTROPY.catastrophic_error s
        | ENTROPY.success entropy_input entropy_stream =>
          let new_working_state := reseed_algorithm working_state entropy_input additional_input in
          ENTROPY.success (new_working_state, security_strength, prediction_resistance_flag) entropy_stream
      end
  end.

Inductive DRBG_generate_algorithm_result :=
| generate_algorithm_reseed_required: DRBG_generate_algorithm_result
| generate_algorithm_success: list byte -> DRBG_working_state -> DRBG_generate_algorithm_result.

Fixpoint DRBG_generate_function_helper (generate_algorithm: DRBG_working_state -> Z -> list byte -> DRBG_generate_algorithm_result)
          (reseed_function: ENTROPY.stream -> DRBG_state_handle -> bool -> list byte -> ENTROPY.result DRBG_state_handle)
          (entropy_stream: ENTROPY.stream) (state_handle: DRBG_state_handle) (requested_number_of_bytes: Z)
          (prediction_resistance_request: bool) (additional_input: list byte) (should_reseed: bool) (count: nat): ENTROPY.result (list byte * DRBG_working_state) :=
  let result := if should_reseed then
                        match reseed_function entropy_stream state_handle prediction_resistance_request additional_input with
                          | ENTROPY.success x entropy_stream => ENTROPY.success (x, []) entropy_stream
                          | ENTROPY.error e entropy_stream => ENTROPY.error e entropy_stream
                        end
                      else ENTROPY.success (state_handle, additional_input) entropy_stream in
  match result with
    | ENTROPY.error e s => ENTROPY.error e s
    | ENTROPY.success (state_handle, additional_input) entropy_stream =>
      match state_handle with (working_state, security_strength, prediction_resistance_flag) =>
        match generate_algorithm working_state requested_number_of_bytes additional_input with
          | generate_algorithm_reseed_required =>
            match count with
              | O => ENTROPY.error ENTROPY.generic_error entropy_stream (* impossible *)
              | S count' => DRBG_generate_function_helper generate_algorithm reseed_function
                                entropy_stream state_handle requested_number_of_bytes
                                prediction_resistance_request additional_input true count'
            end
          | generate_algorithm_success x y => ENTROPY.success (x, y) entropy_stream
        end
      end
    end.

Definition DRBG_generate_function (generate_algorithm: Z -> DRBG_working_state -> Z -> list byte -> DRBG_generate_algorithm_result)
             (reseed_function: ENTROPY.stream -> DRBG_state_handle -> bool -> list byte -> ENTROPY.result DRBG_state_handle)
             (reseed_interval: Z) (max_number_of_bytes_per_request: Z) (max_additional_input_length: Z)
             (entropy_stream: ENTROPY.stream) (state_handle: DRBG_state_handle)
             (requested_number_of_bytes requested_security_strength: Z)
             (prediction_resistance_request: bool) (additional_input: list byte): ENTROPY.result (list byte * DRBG_state_handle) :=
  match state_handle with (working_state, security_strength, prediction_resistance_flag) =>
    if requested_number_of_bytes >? max_number_of_bytes_per_request then ENTROPY.error ENTROPY.generic_error entropy_stream
    else
      if requested_security_strength >? security_strength then ENTROPY.error ENTROPY.generic_error entropy_stream
      else
        if (Zlength additional_input) >? max_additional_input_length then ENTROPY.error ENTROPY.generic_error entropy_stream
        else
          if prediction_resistance_request && (negb prediction_resistance_flag) then ENTROPY.error ENTROPY.generic_error entropy_stream
          else
            match DRBG_generate_function_helper (generate_algorithm reseed_interval) reseed_function
                       entropy_stream state_handle requested_number_of_bytes prediction_resistance_request
                       additional_input prediction_resistance_request 1%nat with
              | ENTROPY.error e s => ENTROPY.error e s
              | ENTROPY.success (output, new_working_state) entropy_stream =>
                  ENTROPY.success (output, (new_working_state, security_strength, prediction_resistance_flag)) entropy_stream
            end
  end.