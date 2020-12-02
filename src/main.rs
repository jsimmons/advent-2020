#![cfg_attr(feature = "nightly", feature(asm))]
#![feature(test)]

pub mod counters;

use std::{
    cmp::Ordering,
    fmt::Debug,
    fs::File,
    io::{BufRead, BufReader, Read},
};

use counters::Counter;

fn read_numbers<R: Read>(read: R) -> Vec<i64> {
    BufReader::new(read)
        .lines()
        .filter_map(|line| line.ok()?.parse().ok())
        .collect()
}

struct Runner {
    time_counter: Counter,
    inst_counter: Counter,
}

impl Runner {
    fn new() -> Self {
        Self {
            time_counter: Counter::by_name("wall-time").unwrap(),
            inst_counter: Counter::by_name("instructions-minus-irqs:u").unwrap(),
        }
    }

    #[inline]
    fn bench<T: Debug, F: FnOnce() -> T>(&self, name: &str, f: F) -> T {
        let start_time = self.time_counter.since_start();
        let start = self.inst_counter.since_start();
        let result = f();
        let end = self.inst_counter.since_start();
        let end_time = self.time_counter.since_start();
        let instructions = end - start;
        let nanoseconds = end_time - start_time;

        println!(
            "{}\n\tresult: {:?}\n\tinstuctions: {}\n\tnanoseconds: {}",
            name, result, instructions, nanoseconds,
        );

        result
    }
}

fn main() {
    let runner = Runner::new();

    // DAY 1
    {
        let input = {
            let file = File::open("data/01.txt").expect("unable to find day 1 data");
            let mut input = read_numbers(file);
            input.sort();
            input
        };

        let result = runner.bench("day 1, part 1", || {
            let mut a = input.iter();
            let mut b = input.iter().rev();
            let mut x = *a.next()?;
            let mut y = *b.next()?;
            loop {
                match (x + y).cmp(&2020) {
                    Ordering::Less => x = *a.next()?,
                    Ordering::Greater => y = *b.next()?,
                    Ordering::Equal => return Some(x * y),
                }
            }
        });

        assert_eq!(result, Some(889779));

        let result = runner.bench("day 1, part 2", || {
            let min = *input.first()?;
            let mut lookup = [0; 2020];

            for (i, &x) in input.iter().enumerate() {
                for &y in &input[i + 1..] {
                    if x + y + min < 2020 {
                        lookup[(x + y) as usize] = x;
                    }
                }
            }
            let lookup = lookup;

            for &z in &input {
                let diff = 2020 - z;
                let x = lookup[diff as usize];
                if x != 0 {
                    let y = diff - x;
                    return Some(x * y * z);
                }
            }

            None
        });

        assert_eq!(result, Some(76110336));
    }
}
