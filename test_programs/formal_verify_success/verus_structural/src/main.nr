struct Thing {}

struct Car<T> {
    passengers: T,
    four_doors: bool,
}

#['ensures(result)]
fn identical_car_instances() -> bool {
    let car_one: Car<Thing> = Car { passengers: Thing {}, four_doors: true };
    let car_two: Car<Thing> = Car { passengers: Thing {}, four_doors: true };

    let Car { passengers: _, four_doors: first_doors } = car_one;
    let Car { passengers: _, four_doors: second_doors } = car_two;

    assert(first_doors);
    assert(second_doors);

    let doors_match = first_doors == second_doors;
    assert(doors_match);
    doors_match
}

#['ensures(result)]
fn generic_car_instances(passengers: u32) -> bool {
    let car_one: Car<u32> = Car { passengers, four_doors: true };
    let car_two: Car<u32> = Car { passengers, four_doors: true };

    let Car { passengers: first_passengers, four_doors: first_doors } = car_one;
    let Car { passengers: second_passengers, four_doors: second_doors } = car_two;

    let passengers_match = first_passengers == second_passengers;
    let doors_match = first_doors == second_doors;

    assert(passengers_match);
    assert(doors_match);

    passengers_match & doors_match
}

#['ensures(result)]
fn main() -> pub bool {
    let thing_case = identical_car_instances();
    let generic_case = generic_car_instances(42);

    thing_case & generic_case
}
