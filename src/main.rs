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

struct Lexer<'a> {
    bytes: &'a [u8],
    index: usize,
}

impl<'a> Lexer<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, index: 0 }
    }

    fn num(&mut self) -> usize {
        let mut acc = 0;
        while let Some(&b) = self.bytes.get(self.index) {
            let digit = b.wrapping_sub(b'0');
            if digit <= 9 {
                acc = acc * 10 + digit as usize;
                self.index += 1;
            } else {
                break;
            }
        }
        acc
    }

    fn byte(&mut self) -> u8 {
        if let Some(&b) = self.bytes.get(self.index) {
            self.index += 1;
            b
        } else {
            0
        }
    }

    fn skip_bytes(&mut self, count: usize) {
        self.index += count;
    }

    fn remaining(&self) -> &'a [u8] {
        &self.bytes[self.index..]
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
                    let mut lexer = Lexer::new(line.as_bytes());
                    let min = lexer.num();
                    lexer.skip_bytes(1);
                    let max = lexer.num();
                    lexer.skip_bytes(1);
                    let letter = lexer.byte();
                    lexer.skip_bytes(2);
                    let password = lexer.remaining();
                    let count = password.iter().filter(|&&b| b == letter).count();
                    count >= min && count <= max
                })
                .count()
        });

        assert_eq!(result, 560);

        let result = runner.bench("day 2, part 2", || {
            data.lines()
                .filter(|&line| {
                    let mut lexer = Lexer::new(line.as_bytes());
                    let i = lexer.num();
                    lexer.skip_bytes(1);
                    let j = lexer.num();
                    lexer.skip_bytes(1);
                    let letter = lexer.byte();
                    lexer.skip_bytes(2);
                    let password = lexer.remaining();
                    (password[i - 1] == letter) ^ (password[j - 1] == letter)
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
