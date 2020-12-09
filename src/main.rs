#![cfg_attr(feature = "nightly", feature(asm))]
#![feature(test)]
#![feature(iterator_fold_self)]
#![feature(str_split_once)]
#![feature(slice_fill)]
#![feature(array_windows)]

pub mod counters;

use std::{cmp::Ordering, collections::HashMap, fmt::Debug, time::Duration};

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

        let result_fmt = format!("{:?}", result);
        let duration_fmt = format!("{:?}", Duration::from_nanos(nanoseconds));
        println!(
            " {:<14} | {:<15} | {:<15} | {:<15}",
            name, result_fmt, duration_fmt, instructions,
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

    println!(
        "{:<15} | {:<15} | {:<15} | {:<15}",
        "", "Result", "Duration", "Instructions",
    );

    println!("{:-^1$}", "", 67);

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
            seats
                .windows(2)
                .find_map(|w| {
                    if w[0] + 1 != w[1] {
                        Some(w[0] + 1)
                    } else {
                        None
                    }
                })
                .unwrap()
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
                        .fold_first(|acc, elem| acc & elem)
                        .unwrap_or(0)
                        .count_ones()
                })
                .sum::<u32>()
        });

        assert_eq!(result, 3550);
    }

    // Day 7
    {
        let data = load_day(7);

        type Bags<'a> = HashMap<&'a str, Vec<(&'a str, u32)>>;

        fn parse_bags(data: &str) -> Bags {
            data.lines()
                .map(|line| {
                    let (bag, rest) = line.split_once(" bags contain ").unwrap();
                    (
                        bag,
                        rest.trim_end_matches('.')
                            .split(", ")
                            .filter_map(|e| {
                                let (count, rest) = e.split_once(' ').unwrap();
                                Some((rest[..rest.len() - 4].trim(), count.parse::<u32>().ok()?))
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<HashMap<_, _>>()
        }

        let result = runner.bench("day 7, part 1", || {
            fn has<'v, 'a>(v: &'v mut HashMap<&'a str, bool>, bags: &'a Bags, b: &'a str) -> bool {
                v.get(b).copied().unwrap_or_else(|| {
                    let f = b == "shiny gold" || bags[b].iter().any(|(b, _)| has(v, bags, b));
                    v.insert(b, f);
                    f
                })
            }
            let bags = parse_bags(&data);
            let mut v = HashMap::new();
            bags.keys().filter(|b| has(&mut v, &bags, b)).count() - 1
        });

        assert_eq!(result, 238);

        let result = runner.bench("day 7, part 2", || {
            fn count(bags: &Bags, b: &str) -> u32 {
                bags[b].iter().map(|(b, c)| c * count(bags, b)).sum::<u32>() + 1
            }
            let bags = parse_bags(&data);
            count(&bags, "shiny gold") - 1
        });

        assert_eq!(result, 82930);
    }

    // Day 8
    {
        let data = load_day(8);

        let parse_code = || {
            data.lines()
                .map(|l| {
                    let operand = l[4..].parse().unwrap();
                    match l.as_bytes()[0] {
                        b'n' => Instruction::Nop(operand),
                        b'j' => Instruction::Jmp(operand),
                        b'a' => Instruction::Acc(operand),
                        _ => panic!("unknown instruction"),
                    }
                })
                .collect::<Vec<_>>()
        };

        #[derive(Copy, Clone)]
        enum Instruction {
            Nop(isize),
            Jmp(isize),
            Acc(isize),
        }

        struct VM<'c> {
            code: &'c [Instruction],
            ip: usize,
            acc: isize,
            swap: usize,
        }

        impl<'c> VM<'c> {
            fn new(code: &'c [Instruction], swap: usize) -> Self {
                VM {
                    code,
                    ip: 0,
                    acc: 0,
                    swap,
                }
            }

            fn running(&self) -> bool {
                self.ip < self.code.len()
            }

            fn exec(&mut self) {
                match self.code[self.ip] {
                    Instruction::Nop(operand) => {
                        let operand = if self.ip == self.swap { operand } else { 1 };
                        self.ip = self.ip.wrapping_add(operand as usize);
                    }
                    Instruction::Jmp(operand) => {
                        let operand = if self.ip == self.swap { 1 } else { operand };
                        self.ip = self.ip.wrapping_add(operand as usize);
                    }
                    Instruction::Acc(operand) => {
                        self.acc += operand;
                        self.ip = self.ip.wrapping_add(1);
                    }
                }
            }
        }

        let result = runner.bench("day 8, part 1", || {
            let code = parse_code();
            let mut visited = vec![0u8; code.len()];
            let mut vm = VM::new(&code, usize::MAX);
            while vm.running() && visited[vm.ip] == 0 {
                visited[vm.ip] += 1;
                vm.exec();
            }
            vm.acc
        });

        assert_eq!(result, 1489);

        let result = runner.bench("day 8, part 2", || {
            let code = parse_code();
            let mut visited = vec![0u8; code.len()];
            'outer: for swap in code
                .iter()
                .enumerate()
                .filter_map(|(i, instr)| match instr {
                    Instruction::Acc(_) => None,
                    _ => Some(i),
                })
            {
                let mut vm = VM::new(&code, swap);
                while vm.running() {
                    if visited[vm.ip] != 0 {
                        visited.fill(0);
                        continue 'outer;
                    }
                    visited[vm.ip] += 1;
                    vm.exec();
                }
                return vm.acc;
            }
            0
        });

        assert_eq!(result, 1539);
    }

    // Day 9
    {
        let data = load_day(9);

        let result = runner.bench("day 9, part 1", || {
            let numbers = data
                .lines()
                .filter_map(|l| l.parse().ok())
                .collect::<Vec<i32>>();

            numbers
                .array_windows()
                .find_map(|x: &[i32; 26]| {
                    let mut window = [0; 25];
                    window.clone_from_slice(&x[..25]);
                    let search = x[25];
                    window.sort();

                    let mut i = 0;
                    let mut j = 24;
                    let mut found = false;
                    while i != j {
                        match (window[j] + window[i]).cmp(&search) {
                            Ordering::Less => i += 1,
                            Ordering::Greater => j -= 1,
                            Ordering::Equal => {
                                found = true;
                                break;
                            }
                        }
                    }

                    if !found {
                        Some(search)
                    } else {
                        None
                    }
                })
                .unwrap()
        });

        assert_eq!(result, 20874512);

        let result = runner.bench("day 9, part 1", || {
            let numbers = data
                .lines()
                .filter_map(|l| l.parse().ok())
                .collect::<Vec<i32>>();

            let target = 20874512;
            let mut i = 0;
            let mut j = 0;

            while i < numbers.len() {
                let mut sum = 0;
                while sum < target && j < numbers.len() {
                    sum += numbers[j];
                    j += 1;
                }
                if sum == target {
                    break;
                }
                i += 1;
                j = i;
            }
            let range = &numbers[i..j];
            range.iter().min().unwrap() + range.iter().max().unwrap()
        });

        assert_eq!(result, 3012420);
    }
}
