// ============================================================================
// Shared arithmetic and scan helpers for the complementary-triples computation package.
//
// This file contains reusable arithmetic support used by the scan and
// presentation routines.
// ============================================================================


// List the primes up to the given norm bound where the quaternion algebra splits.
function split_primes_up_to(order_data, norm_bound)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);
    split_primes := [];

    if Type(norm_bound) ne RngIntElt or norm_bound lt 0 then
        error "norm_bound must be an integer >= 0.";
    end if;

    if norm_bound lt 1 then
        return split_primes;
    end if;

    if Type(integer_ring) eq RngInt then
        for prime_integer in [2..norm_bound] do
            if not IsPrime(prime_integer) then
                continue;
            end if;

            if algebra_discriminant mod prime_integer eq 0 then
                continue;
            end if;

            Append(~split_primes, ideal<integer_ring | prime_integer>);
        end for;

        return split_primes;
    end if;

    for prime_ideal in IdealsUpTo(norm_bound, integer_ring) do
        if not IsPrime(prime_ideal) then
            continue;
        end if;

        if Valuation(algebra_discriminant, prime_ideal) ne 0 then
            continue;
        end if;

        Append(~split_primes, prime_ideal);
    end for;

    return split_primes;
end function;


// Return the finite primes where the quaternion algebra is ramified.
function ramified_primes(order_data)
    integer_ring := order_data`integer_ring;
    algebra_discriminant := Discriminant(order_data`quaternion_algebra);

    if Type(integer_ring) eq RngInt then
        return [ideal<integer_ring | factor[1]> : factor in Factorization(algebra_discriminant)];
    end if;

    return [factor[1] : factor in Factorization(algebra_discriminant)];
end function;


// Normalize principal generators so the same ideal gets the same key.
function normalized_ideal_generator_for_key(generator)
    coefficients := Eltseq(generator);

    for coefficient in coefficients do
        if coefficient eq 0 then
            continue;
        end if;

        if coefficient lt 0 then
            return -generator;
        end if;

        return generator;
    end for;

    return generator;
end function;


// Use a textual ideal key so ideals from distinct but isomorphic ring instances
// can be deduplicated in skipped-task and report aggregation.
function ideal_key(ideal_x)
    order_key := Sprint(Order(ideal_x));
    has_generator, generator := IsPrincipal(ideal_x);

    if has_generator then
        generator := normalized_ideal_generator_for_key(generator);
        return Sprintf(
            "%o || principal || %o || %o",
            order_key,
            Norm(ideal_x),
            Eltseq(generator)
        );
    end if;

    return Sprintf("%o || %o", order_key, Sprint(ideal_x));
end function;


procedure append_skipped_task_if_new(task_key, modulus_ideal, estimated_seconds, ~skipped_task_list)
    modulus_key := ideal_key(modulus_ideal);

    for existing_entry in skipped_task_list do
        if (existing_entry[1] eq task_key) and (ideal_key(existing_entry[2]) eq modulus_key) then
            return;
        end if;
    end for;

    Append(~skipped_task_list, <task_key, modulus_ideal, estimated_seconds>);
end procedure;


procedure append_prime_if_new(prime_ideal, ~prime_list)
    prime_key := ideal_key(prime_ideal);

    for existing_prime in prime_list do
        if ideal_key(existing_prime) eq prime_key then
            return;
        end if;
    end for;

    Append(~prime_list, prime_ideal);
end procedure;


procedure append_ideal_if_new(ideal_x, ~ideal_list)
    ideal_x_key := ideal_key(ideal_x);

    for existing_ideal in ideal_list do
        if ideal_key(existing_ideal) eq ideal_x_key then
            return;
        end if;
    end for;

    Append(~ideal_list, ideal_x);
end procedure;


function validated_index_range(index_range)
    if Type(index_range) ne SeqEnum or #index_range ne 2 then
        error "index_range must be a sequence [a, b].";
    end if;

    if Type(index_range[1]) ne RngIntElt or Type(index_range[2]) ne RngIntElt then
        error "The endpoints of index_range must be integers.";
    end if;

    if index_range[1] gt index_range[2] then
        error "index_range must satisfy a <= b.";
    end if;

    return index_range[1], index_range[2];
end function;
