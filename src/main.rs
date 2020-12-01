#![cfg_attr(feature = "nightly", feature(asm))]

use std::{
    fs::File,
    io::{BufRead, BufReader, Read},
};

use counters::Counter;

pub mod counters;

fn read_numbers<R: Read>(io: R) -> Vec<i32> {
    let buf_reader = BufReader::new(io);
    buf_reader
        .lines()
        .filter_map(|line| line.ok())
        .filter_map(|line| line.parse().ok())
        .collect()
}

fn day_1_part_1(input: &[i32]) -> i32 {
    input
        .iter()
        .enumerate()
        .find_map(|(i, x)| {
            input[i + 1..]
                .iter()
                .find_map(|y| if x + y == 2020 { Some(x * y) } else { None })
        })
        .unwrap()
}

fn day_1_part_2(input: &[i32]) -> i32 {
    input
        .iter()
        .enumerate()
        .find_map(|(i, x)| {
            input[i + 1..].iter().enumerate().find_map(|(j, y)| {
                input[i + j + 2..].iter().find_map(|z| {
                    if x + y + z == 2020 {
                        Some(x * y * z)
                    } else {
                        None
                    }
                })
            })
        })
        .unwrap()
}

fn main() {
    let day_1_input =
        read_numbers(File::open("data/day_1.txt").expect("unable to find day 1 data"));

    let instruction_counter = Counter::by_name("instructions-minus-irqs:u").unwrap();

    let start = instruction_counter.since_start();
    let day_1_part_1_result = day_1_part_1(&day_1_input);
    let end = instruction_counter.since_start();

    println!(
        "day 1, part 1\nanswer: {}\ninstuctions: {}",
        day_1_part_1_result,
        (end - start)
    );
    assert_eq!(day_1_part_1_result, 889779);

    println!();

    let start = instruction_counter.since_start();
    let day_1_part_2_result = day_1_part_2(&day_1_input);
    let end = instruction_counter.since_start();
    println!(
        "day 1, part 2\nanswer: {}\ninstuctions: {}",
        day_1_part_2_result,
        (end - start)
    );
    assert_eq!(day_1_part_2_result, 76110336);
}
