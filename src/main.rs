#![cfg_attr(feature = "nightly", feature(asm))]
#![feature(test)]

pub mod counters;

use std::{
    cmp::Ordering,
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
    fn bench<T, F: FnOnce() -> T>(&self, f: F) -> (T, u64, u64) {
        let start_time = self.time_counter.since_start();
        let start = self.inst_counter.since_start();
        let result = f();
        let end = self.inst_counter.since_start();
        let end_time = self.time_counter.since_start();
        (result, (end_time - start_time), (end - start))
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

        let (result, nanoseconds, instructions) = runner.bench(|| {
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

        println!(
            "day 1, part 1\nanswer: {}\ninstuctions: {}\nnanoseconds: {}",
            result.unwrap(),
            instructions,
            nanoseconds,
        );
        println!();

        assert_eq!(result, Some(889779));

        // let (result, instructions) = runner.bench(|| {
        //     let min = *input.first()?;
        //     let mut lookup = Vec::with_capacity(input.len() * (input.len() - 1));
        //     for i in 0..input.len() {
        //         let x = input[i];
        //         for j in (i + 1)..input.len() {
        //             let y = input[j];
        //             if x + y + min < 2020 {
        //                 lookup.push((x + y, x))
        //             }
        //         }
        //     }
        //     lookup.sort_by_key(|x| x.0);
        //     let lookup = lookup;

        //     for &z in &input {
        //         let diff = 2020 - z;
        //         if let Ok(index) = lookup.binary_search_by_key(&diff, |x| x.0) {
        //             let (s, x) = lookup[index];
        //             let y = s - x;
        //             return Some(x * y * z);
        //         }
        //     }

        //     None
        // });

        // let (result, instructions) = runner.bench(|| {
        //     let min = *input.first()?;
        //     let mut lookup = HashMap::with_capacity(input.len() * (input.len() - 1));
        //     for i in 0..input.len() {
        //         let x = input[i];
        //         for j in (i + 1)..input.len() {
        //             let y = input[j];
        //             if x + y + min < 2020 {
        //                 lookup.insert(x + y, x);
        //             }
        //         }
        //     }
        //     let lookup = lookup;

        //     for &z in &input {
        //         let diff = 2020 - z;
        //         if let Some(x) = lookup.get(&diff) {
        //             let y = diff - x;
        //             return Some(x * y * z);
        //         }
        //     }

        //     None
        // });

        let (result, nanoseconds, instructions) = runner.bench(|| {
            let min = *input.first()?;
            let mut lookup = [0; 2020];
            for i in 0..input.len() {
                let x = input[i];
                for j in (i + 1)..input.len() {
                    let y = input[j];
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

        println!(
            "day 1, part 2\nanswer: {}\ninstuctions: {}\nnanoseconds: {}",
            result.unwrap(),
            instructions,
            nanoseconds,
        );
        println!();

        assert_eq!(result, Some(76110336));
    }
}
