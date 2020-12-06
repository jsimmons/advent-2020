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
            "{}\n\tresult: {:?}\n\tinstructions: {}\n\tnanoseconds: {}",
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

    fn bytes_to(&mut self, needle: &[u8]) -> &[u8] {
        let start_index = self.index;

        let end_index = if let Some(found_index) = &self.bytes[self.index..]
            .iter()
            .position(|b| needle.contains(b))
        {
            self.index = start_index + found_index + 1;
            start_index + found_index
        } else {
            self.index = self.bytes.len();
            self.bytes.len()
        };

        &self.bytes[start_index..end_index]
    }

    fn field(&mut self) -> &[u8] {
        self.skip_ws();
        self.bytes_to(&[b':', b' ', b'\n'])
    }

    fn skip_ws(&mut self) {
        while let Some(&b) = self.bytes.get(self.index) {
            if b != b' ' || b != b'\n' {
                break;
            }
            self.index += 1;
        }
    }

    fn skip_bytes(&mut self, count: usize) {
        self.index += count;
    }

    fn is_empty(&self) -> bool {
        self.index >= self.bytes.len() - 1
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
            let lines = data
                .lines()
                .map(|line| {
                    line.as_bytes()
                        .iter()
                        .fold(0, |acc, &b| acc << 1 | (b == b'#') as u32)
                })
                .collect::<Vec<_>>();

            let rotr31 = |x: u32, count: usize| -> u32 { x >> count | x << (31 - count) };

            [(1, 1), (3, 1), (5, 1), (7, 1), (1, 2)]
                .iter()
                .map(|&(dx, dy)| {
                    lines
                        .iter()
                        .step_by(dy)
                        .fold(
                            (0b0100_0000_0000_0000_0000_0000_0000_0000, 0),
                            |(mask, count), &line| {
                                let tree = line & mask != 0;
                                (rotr31(mask, dx), count + tree as u64)
                            },
                        )
                        .1
                })
                .product::<u64>()
        });

        assert_eq!(result, 3316272960);
    }

    // Day 4
    {
        let data = load_day(4);

        let result = runner.bench("day 4, part 1", || {
            data.split("\n\n")
                .filter(|&passport| {
                    let mut lexer = Lexer::new(passport.as_bytes());
                    let mut valid_fields = 0;
                    while lexer.is_empty() == false {
                        match lexer.field() {
                            b"byr" | b"iyr" | b"eyr" | b"hgt" | b"hcl" | b"ecl" | b"pid" => {
                                valid_fields += 1;
                            }
                            _ => {}
                        }

                        let _ = lexer.field();
                    }
                    valid_fields == 7
                })
                .count()
        });

        assert_eq!(result, 256);

        let result = runner.bench("day 4, part 2", || {
            data.split("\n\n")
                .filter(|&passport| {
                    let mut lexer = Lexer::new(passport.as_bytes());

                    let valid_num = |slice: &[u8], min, max| {
                        std::str::from_utf8(slice)
                            .unwrap()
                            .parse::<i32>()
                            .map_or(false, |num| num >= min && num <= max)
                    };

                    let valid_num_4 = |slice: &[u8], min, max| {
                        if slice.len() == 4 {
                            valid_num(slice, min, max)
                        } else {
                            false
                        }
                    };

                    let mut valid_count = 0;
                    while lexer.is_empty() == false {
                        let valid = match lexer.field() {
                            b"byr" => valid_num_4(lexer.field(), 1920, 2002),
                            b"iyr" => valid_num_4(lexer.field(), 2010, 2020),
                            b"eyr" => valid_num_4(lexer.field(), 2020, 2030),
                            b"hgt" => match lexer.field() {
                                [num @ .., b'c', b'm'] => valid_num(num, 150, 193),
                                [num @ .., b'i', b'n'] => valid_num(num, 59, 76),
                                _ => false,
                            },
                            b"hcl" => match lexer.field() {
                                [b'#', digits @ ..] => {
                                    digits.len() == 6
                                        && digits.iter().all(|&b| match b {
                                            b'0'..=b'9' | b'a'..=b'f' => true,
                                            _ => false,
                                        })
                                }
                                _ => false,
                            },
                            b"ecl" => match lexer.field() {
                                b"amb" | b"blu" | b"brn" | b"gry" | b"grn" | b"hzl" | b"oth" => {
                                    true
                                }
                                _ => false,
                            },
                            b"pid" => {
                                let field = lexer.field();
                                field.len() == 9
                                    && field.iter().all(|&b| match b {
                                        b'0'..=b'9' => true,
                                        _ => false,
                                    })
                            }
                            b"cid" => {
                                let _ = lexer.field();
                                valid_count -= 1;
                                true
                            }
                            _ => false,
                        };

                        if valid {
                            valid_count += 1;
                        } else {
                            break;
                        }
                    }

                    valid_count == 7
                })
                .count()
        });

        assert_eq!(result, 198);
    }

    // Day 5
    {
        let data = load_day(5);

        let to_num = |line: &str| {
            line.as_bytes().iter().fold(0, |acc, &elem| {
                (acc << 1) | (elem == b'B' || elem == b'R') as u32
            })
        };

        let result = runner.bench("day 5, part 1", || data.lines().map(to_num).max().unwrap());

        assert_eq!(result, 896);

        let result = runner.bench("day 5, part 2", || {
            let mut seats = data.lines().map(to_num).collect::<Vec<_>>();
            seats.sort_unstable();
            let mut seat = seats[0];
            for &occupied_seat in &seats[1..seats.len() - 1] {
                seat += 1;
                if seat != occupied_seat {
                    break;
                }
            }
            seat
        });

        assert_eq!(result, 659);
    }

    // Day 6
    {
        let data = load_day(6);

        let mask = |acc, &elem| acc | 1u32 << (elem - b'a');

        let result = runner.bench("day 6, part 1", || {
            data.split("\n\n")
                .map(|g| g.lines().flat_map(str::as_bytes).fold(0, mask).count_ones())
                .sum::<u32>()
        });

        assert_eq!(result, 6885);

        let result = runner.bench("day 6, part 2", || {
            data.split("\n\n")
                .map(|g| {
                    g.lines()
                        .map(|l| l.as_bytes().iter().fold(0, mask))
                        .fold(!0, |acc, elem| acc & elem)
                        .count_ones()
                })
                .sum::<u32>()
        });

        assert_eq!(result, 3550);
    }
}
