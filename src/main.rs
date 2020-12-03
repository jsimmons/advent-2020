#![cfg_attr(feature = "nightly", feature(asm))]
#![feature(test)]

pub mod counters;

use std::{cmp::Ordering, fmt::Debug};

use counters::Counter;

fn load_day(day: i32) -> String {
    let file_name = format!("data/{:02}.txt", day);
    std::fs::read_to_string(file_name).expect("unable to load data")
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
        let data = load_day(1);

        let result = runner.bench("day 1, part 1", || {
            let mut data = data
                .lines()
                .filter_map(|line| line.parse().ok())
                .collect::<Vec<i64>>();
            data.sort_unstable();
            let data = data;

            let mut a = data.iter();
            let mut b = data.iter().rev();
            let mut x = *a.next().unwrap();
            let mut y = *b.next().unwrap();
            loop {
                match (x + y).cmp(&2020) {
                    Ordering::Less => x = *a.next().unwrap(),
                    Ordering::Greater => y = *b.next().unwrap(),
                    Ordering::Equal => return x * y,
                }
            }
        });

        assert_eq!(result, 889779);

        let result = runner.bench("day 1, part 2", || {
            let mut data = data
                .lines()
                .filter_map(|line| line.parse().ok())
                .collect::<Vec<i64>>();
            data.sort_unstable();
            let data = data;

            let min = *data.first().unwrap();
            let mut lookup = [0; 2020];

            for (i, &x) in data.iter().enumerate() {
                for &y in &data[i + 1..] {
                    if x + y + min < 2020 {
                        lookup[(x + y) as usize] = x;
                    }
                }
            }

            for &z in &data {
                let diff = 2020 - z;
                let x = lookup[diff as usize];
                if x != 0 {
                    let y = diff - x;
                    return x * y * z;
                }
            }

            0
        });

        assert_eq!(result, 76110336);
    }

    // Day 2
    {
        let data = load_day(2);

        let result = runner.bench("day 2, part 1", || {
            data.lines()
                .filter(|line| {
                    let dash = line.find('-').unwrap();
                    let space = line.find(' ').unwrap();
                    let min = line[0..dash].parse().unwrap();
                    let max = line[dash + 1..space].parse().unwrap();
                    let bytes = line.as_bytes();
                    let letter = bytes[space + 1];
                    let count = bytes.iter().filter(|&&b| b == letter).count() - 1;
                    count >= min && count <= max
                })
                .count()
        });

        assert_eq!(result, 560);

        let result = runner.bench("day 2, part 2", || {
            data.lines()
                .filter(|&line| {
                    let dash = line.find('-').unwrap();
                    let space = line.find(' ').unwrap();
                    let i = line[0..dash].parse::<usize>().unwrap() - 1;
                    let j = line[dash + 1..space].parse::<usize>().unwrap() - 1;
                    let bytes = line.as_bytes();
                    let letter = bytes[space + 1];
                    let password = &bytes[space + 4..];
                    ((password[i] == letter) as i32 + (password[j] == letter) as i32) == 1
                })
                .count()
        });

        assert_eq!(result, 303);
    }

    // Day 3
    {
        let data = load_day(3);

        let result = runner.bench("day 3, part 1", || {
            data.lines()
                .enumerate()
                .filter(|&(i, row)| row.as_bytes()[(i * 3) % row.len()] == b'#')
                .count()
        });

        assert_eq!(result, 203);

        let result = runner.bench("day 3, part 2", || {
            let lines = data.lines().collect::<Vec<_>>();
            [(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)]
                .iter()
                .map(|&(step_x, step_y)| {
                    lines
                        .iter()
                        .step_by(step_y)
                        .enumerate()
                        .filter(|&(i, row)| row.as_bytes()[(i * step_x) % row.len()] == b'#')
                        .count() as i64
                })
                .product::<i64>()
        });

        assert_eq!(result, 3316272960);
    }
}
