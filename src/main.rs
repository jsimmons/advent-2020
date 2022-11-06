pub mod counters;

use std::{
    cmp::Ordering,
    collections::{hash_map::DefaultHasher, HashMap},
    convert::TryInto,
    fmt::Debug,
    hash::Hasher,
    marker::PhantomData,
    time::Duration,
};

use counters::Counter;

#[macro_use]
extern crate log;

// Some unstable code from rust stdlib.

/// A windowed iterator over a slice in overlapping chunks (`N` elements at a
/// time), starting at the beginning of the slice
///
/// This struct is created by the [`array_windows`] method on [slices].
///
/// # Example
///
/// ```
/// use narcissus_core::slice::array_windows;
///
/// let slice = [0, 1, 2, 3];
/// let iter = array_windows::<_, 2>(&slice);
/// ```
///
/// [`array_windows`]: slice::array_windows
/// [slices]: slice
#[derive(Debug, Clone, Copy)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct ArrayWindows<'a, T: 'a, const N: usize> {
    slice_head: *const T,
    num: usize,
    marker: PhantomData<&'a [T; N]>,
}

impl<'a, T: 'a, const N: usize> ArrayWindows<'a, T, N> {
    #[inline]
    pub fn new(slice: &'a [T]) -> Self {
        let num_windows = slice.len().saturating_sub(N - 1);
        Self {
            slice_head: slice.as_ptr(),
            num: num_windows,
            marker: PhantomData,
        }
    }
}

impl<'a, T, const N: usize> Iterator for ArrayWindows<'a, T, N> {
    type Item = &'a [T; N];

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.num == 0 {
            return None;
        }
        // SAFETY:
        // This is safe because it's indexing into a slice guaranteed to be length > N.
        let ret = unsafe { &*self.slice_head.cast::<[T; N]>() };
        // SAFETY: Guaranteed that there are at least 1 item remaining otherwise
        // earlier branch would've been hit
        self.slice_head = unsafe { self.slice_head.add(1) };

        self.num -= 1;
        Some(ret)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.num, Some(self.num))
    }

    #[inline]
    fn count(self) -> usize {
        self.num
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.num <= n {
            self.num = 0;
            return None;
        }
        // SAFETY:
        // This is safe because it's indexing into a slice guaranteed to be length > N.
        let ret = unsafe { &*self.slice_head.add(n).cast::<[T; N]>() };
        // SAFETY: Guaranteed that there are at least n items remaining
        self.slice_head = unsafe { self.slice_head.add(n + 1) };

        self.num -= n + 1;
        Some(ret)
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.nth(self.num.checked_sub(1)?)
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for ArrayWindows<'a, T, N> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a [T; N]> {
        if self.num == 0 {
            return None;
        }
        // SAFETY: Guaranteed that there are n items remaining, n-1 for 0-indexing.
        let ret = unsafe { &*self.slice_head.add(self.num - 1).cast::<[T; N]>() };
        self.num -= 1;
        Some(ret)
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<&'a [T; N]> {
        if self.num <= n {
            self.num = 0;
            return None;
        }
        // SAFETY: Guaranteed that there are n items remaining, n-1 for 0-indexing.
        let ret = unsafe { &*self.slice_head.add(self.num - (n + 1)).cast::<[T; N]>() };
        self.num -= n + 1;
        Some(ret)
    }
}

/// Returns an iterator over overlapping windows of `N` elements of  a slice,
/// starting at the beginning of the slice.
///
/// This is the const generic equivalent of [`windows`].
///
/// If `N` is greater than the size of the slice, it will return no windows.
///
/// # Panics
///
/// Panics if `N` is 0. This check will most probably get changed to a compile time
/// error before this method gets stabilized.
///
/// # Examples
///
/// ```
/// use narcissus_core::slice::array_windows;
///
/// let slice = [0, 1, 2, 3];
/// let mut iter = array_windows(&slice);
/// assert_eq!(iter.next().unwrap(), &[0, 1]);
/// assert_eq!(iter.next().unwrap(), &[1, 2]);
/// assert_eq!(iter.next().unwrap(), &[2, 3]);
/// assert!(iter.next().is_none());
/// ```
///
/// [`windows`]: slice::windows
#[inline]
pub fn array_windows<T, const N: usize>(slice: &[T]) -> ArrayWindows<'_, T, N> {
    assert_ne!(N, 0);
    ArrayWindows::new(slice)
}

fn load_day(day: usize) -> String {
    let file_name = format!("data/{:02}.txt", day);
    std::fs::read_to_string(file_name).expect("unable to load data")
}

fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut hasher = DefaultHasher::new();
    hasher.write(bytes);
    hasher.finish()
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

#[inline(never)]
fn day_01_part_1(data: &str) -> i64 {
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
}

#[inline(never)]
fn day_01_part_2(data: &str) -> i64 {
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
}

#[inline(never)]
fn day_02_part_1(data: &str) -> i64 {
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
        .count() as i64
}

#[inline(never)]
fn day_02_part_2(data: &str) -> i64 {
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
        .count() as i64
}

#[inline(never)]
fn day_03_part_1(data: &str) -> i64 {
    data.lines()
        .enumerate()
        .filter(|&(i, row)| row.as_bytes()[(i * 3) % row.len()] == b'#')
        .count() as i64
}

#[inline(never)]
fn day_03_part_2(data: &str) -> i64 {
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
                        (rotr31(mask, dx), count + tree as i64)
                    },
                )
                .1
        })
        .product()
}

#[inline(never)]
fn day_04_part_1(data: &str) -> i64 {
    data.split("\n\n")
        .filter(|&passport| {
            let mut lexer = Lexer::new(passport.as_bytes());
            let mut valid_fields = 0;
            while !lexer.is_empty() {
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
        .count() as i64
}

#[inline(never)]
fn day_04_part_2(data: &str) -> i64 {
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
            while !lexer.is_empty() {
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
                                && digits
                                    .iter()
                                    .all(|&b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
                        }
                        _ => false,
                    },
                    b"ecl" => matches!(
                        lexer.field(),
                        b"amb" | b"blu" | b"brn" | b"gry" | b"grn" | b"hzl" | b"oth"
                    ),
                    b"pid" => {
                        let field = lexer.field();
                        field.len() == 9 && field.iter().all(|&b| matches!(b, b'0'..=b'9'))
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
        .count() as i64
}

#[inline(never)]
fn day_05_part_1(data: &str) -> i64 {
    data.lines()
        .map(|line: &str| {
            let b = line.as_bytes();
            ((b[9] == b'B') as u32 | (b[9] == b'R') as u32)
                | ((b[8] == b'B') as u32 | (b[8] == b'R') as u32) << 1
                | ((b[7] == b'B') as u32 | (b[7] == b'R') as u32) << 2
                | ((b[6] == b'B') as u32 | (b[6] == b'R') as u32) << 3
                | ((b[5] == b'B') as u32 | (b[5] == b'R') as u32) << 4
                | ((b[4] == b'B') as u32 | (b[4] == b'R') as u32) << 5
                | ((b[3] == b'B') as u32 | (b[3] == b'R') as u32) << 6
                | ((b[2] == b'B') as u32 | (b[2] == b'R') as u32) << 7
                | ((b[1] == b'B') as u32 | (b[1] == b'R') as u32) << 8
                | ((b[0] == b'B') as u32 | (b[0] == b'R') as u32) << 9
        })
        .max()
        .unwrap() as i64
}

#[inline(never)]
fn day_05_part_2(data: &str) -> i64 {
    let mut seats = data
        .lines()
        .map(|line: &str| {
            let b = line.as_bytes();
            ((b[9] == b'B') as u32 | (b[9] == b'R') as u32)
                | ((b[8] == b'B') as u32 | (b[8] == b'R') as u32) << 1
                | ((b[7] == b'B') as u32 | (b[7] == b'R') as u32) << 2
                | ((b[6] == b'B') as u32 | (b[6] == b'R') as u32) << 3
                | ((b[5] == b'B') as u32 | (b[5] == b'R') as u32) << 4
                | ((b[4] == b'B') as u32 | (b[4] == b'R') as u32) << 5
                | ((b[3] == b'B') as u32 | (b[3] == b'R') as u32) << 6
                | ((b[2] == b'B') as u32 | (b[2] == b'R') as u32) << 7
                | ((b[1] == b'B') as u32 | (b[1] == b'R') as u32) << 8
                | ((b[0] == b'B') as u32 | (b[0] == b'R') as u32) << 9
        })
        .collect::<Vec<_>>();
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
        .unwrap() as i64
}

#[inline(never)]
fn day_06_part_1(data: &str) -> i64 {
    data.split("\n\n")
        .map(|g| {
            g.lines()
                .flat_map(str::as_bytes)
                .fold(0, |acc, &elem| acc | 1u32 << (elem - b'a'))
                .count_ones()
        })
        .sum::<u32>() as i64
}

#[inline(never)]
fn day_06_part_2(data: &str) -> i64 {
    data.split("\n\n")
        .map(|g| {
            g.lines()
                .map(|l| {
                    l.as_bytes()
                        .iter()
                        .fold(0, |acc, &elem| acc | 1u32 << (elem - b'a'))
                })
                .reduce(|acc, elem| acc & elem)
                .unwrap_or(0)
                .count_ones()
        })
        .sum::<u32>() as i64
}

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

#[inline(never)]
fn day_07_part_1(data: &str) -> i64 {
    fn has<'v, 'a>(v: &'v mut HashMap<&'a str, bool>, bags: &'a Bags, b: &'a str) -> bool {
        v.get(b).copied().unwrap_or_else(|| {
            let f = b == "shiny gold" || bags[b].iter().any(|(b, _)| has(v, bags, b));
            v.insert(b, f);
            f
        })
    }
    let bags = parse_bags(data);
    let mut v = HashMap::new();
    (bags.keys().filter(|b| has(&mut v, &bags, b)).count() - 1) as i64
}

#[inline(never)]
fn day_07_part_2(data: &str) -> i64 {
    fn count(bags: &Bags, b: &str) -> u32 {
        bags[b].iter().map(|(b, c)| c * count(bags, b)).sum::<u32>() + 1
    }
    let bags = parse_bags(data);
    (count(&bags, "shiny gold") - 1) as i64
}

fn parse_code(data: &str) -> Vec<Instruction> {
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
}

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

#[inline(never)]
fn day_08_part_1(data: &str) -> i64 {
    let code = parse_code(data);
    let mut visited = vec![0u8; code.len()];
    let mut vm = VM::new(&code, usize::MAX);
    while vm.running() && visited[vm.ip] == 0 {
        visited[vm.ip] += 1;
        vm.exec();
    }
    vm.acc as i64
}

#[inline(never)]
fn day_08_part_2(data: &str) -> i64 {
    let code = parse_code(data);
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
        return vm.acc as i64;
    }
    0
}

#[inline(never)]
fn day_09_part_1(data: &str) -> i64 {
    let numbers = data
        .lines()
        .filter_map(|l| l.parse().ok())
        .collect::<Vec<i32>>();

    array_windows(&numbers)
        .find_map(|window: &[i32; 26]| {
            let search = window[25];
            let mut found = false;
            'outer: for (i, &x) in window[0..25].iter().enumerate() {
                for &y in window[i + 1..25].iter() {
                    if x + y == search {
                        found = true;
                        break 'outer;
                    }
                }
            }
            if !found {
                Some(search)
            } else {
                None
            }
        })
        .unwrap() as i64
}

#[inline(never)]
fn day_09_part_2(data: &str) -> i64 {
    let numbers = data
        .lines()
        .filter_map(|l| l.parse().ok())
        .collect::<Vec<i32>>();

    let target = 20874512;
    let mut range = &numbers[..];
    'outer: for (i, &n) in numbers.iter().enumerate() {
        let mut sum = n;
        'inner: for (j, &n) in numbers[i + 1..].iter().enumerate() {
            if sum > target {
                break 'inner;
            }
            if sum == target {
                range = &numbers[i..i + j + 1];
                break 'outer;
            }
            sum += n;
        }
    }
    let mut min = i32::MAX;
    let mut max = i32::MIN;
    for &i in range {
        min = min.min(i);
        max = max.max(i);
    }
    (min + max) as i64
}

#[inline(never)]
fn day_10_part_1(data: &str) -> i64 {
    let mut numbers = data
        .lines()
        .filter_map(|l| l.parse().ok())
        .collect::<Vec<i32>>();
    numbers.sort();
    let (ones, threes) = array_windows(&numbers).fold(
        ((numbers[0] == 1) as i32, (numbers[0] == 3) as i32),
        |(o, t), &[a, b]| (o + ((b - a) == 1) as i32, t + ((b - a) == 3) as i32),
    );
    (ones * (threes + 1)) as i64
}

#[inline(never)]
fn day_10_part_2(data: &str) -> i64 {
    let mut numbers = data
        .lines()
        .filter_map(|l| l.parse().ok())
        .collect::<Vec<i64>>();
    numbers.sort();
    let target = numbers.last().unwrap() + 3;
    numbers.push(target);
    let mut map = HashMap::new();
    map.insert(0, 1);
    for n in numbers {
        map.insert(
            n,
            map.get(&(n - 1)).unwrap_or(&0)
                + map.get(&(n - 2)).unwrap_or(&0)
                + map.get(&(n - 3)).unwrap_or(&0),
        );
    }
    map[&target]
}

#[inline(never)]
fn day_11_part_1(data: &str) -> i64 {
    const FLOOR: u8 = 0;
    const EMPTY: u8 = 1;
    const FULL: u8 = 2;
    const W: usize = 95;
    const H: usize = 95;
    const TRANSITIONS: [u8; 27] = [
        FLOOR, FLOOR, FLOOR, FLOOR, FLOOR, FLOOR, FLOOR, FLOOR, FLOOR, FULL, EMPTY, EMPTY, EMPTY,
        EMPTY, EMPTY, EMPTY, EMPTY, EMPTY, FULL, FULL, FULL, FULL, EMPTY, EMPTY, EMPTY, EMPTY,
        EMPTY,
    ];

    let mut seats = [FLOOR; (W + 2) * (H + 2)];
    for (i, line) in data.lines().enumerate() {
        let mut tmp: [u8; W] = line.as_bytes().try_into().unwrap();
        for b in tmp.iter_mut() {
            *b = match *b {
                b'L' => EMPTY,
                b'#' => FULL,
                _ => FLOOR,
            }
        }
        seats[(i + 1) * (W + 2) + 1..(i + 2) * (W + 2) - 1].copy_from_slice(&tmp);
    }

    let mut tmp = [0; (W + 2) * (H + 2)];
    let mut top = Box::new([0u8; W + 2]);
    let mut mid = Box::new([0u8; W + 2]);
    let mut bot = Box::new([0u8; W + 2]);
    let mut hash = 0;
    loop {
        for (i, &[a, b, c]) in array_windows(&seats).enumerate() {
            tmp[i + 1] = ((a == FULL) as u8) + ((b == FULL) as u8) + ((c == FULL) as u8);
        }

        top.copy_from_slice(&tmp[0..W + 2]);
        mid.copy_from_slice(&tmp[W + 2..2 * (W + 2)]);
        for y in 1..H + 1 {
            bot.copy_from_slice(&tmp[(y + 1) * (W + 2)..(y + 2) * (W + 2)]);
            for x in 0..W + 2 {
                tmp[y * (W + 2) + x] = top[x] + mid[x] + bot[x];
            }
            std::mem::swap(&mut top, &mut mid);
            std::mem::swap(&mut mid, &mut bot);
        }

        for (seat, count) in seats.iter_mut().zip(tmp.iter()) {
            let index = (*seat * 9 + count - (*seat == FULL) as u8) as usize;
            *seat = TRANSITIONS[index];
        }

        let old_hash = hash;
        hash = hash_bytes(&seats);
        if hash == old_hash {
            break;
        }
    }
    seats.iter().copied().filter(|&b| b == FULL).count() as i64
}

#[inline(never)]
fn day_11_part_2(data: &str) -> i64 {
    const W: i32 = 95;
    const H: i32 = 95;

    let mut seats: Vec<u8> = data
        .as_bytes()
        .iter()
        .copied()
        .filter(|&b| b != b'\n')
        .collect();
    assert_eq!(seats.len(), (W * H) as usize);
    let mut tmp = seats.clone();

    fn step(seats: &[u8], tmp: &mut [u8]) -> bool {
        let read = |x, y| {
            if !(0..W).contains(&x) || !(0..H).contains(&y) {
                0
            } else {
                seats[(y * W + x) as usize]
            }
        };
        let mut write = |x, y, v| tmp[(y * W + x) as usize] = v;
        let mut changed = false;
        for y in 0..H {
            for x in 0..W {
                let chair = read(x, y);

                if chair == b'.' {
                    continue;
                }

                let occupied = |dx, dy| {
                    let mut x = x;
                    let mut y = y;
                    loop {
                        x += dx;
                        y += dy;
                        match read(x, y) {
                            b'#' => return 1,
                            b'L' | 0 => return 0,
                            _ => continue,
                        }
                    }
                };
                let count = occupied(-1, -1)
                    + occupied(0, -1)
                    + occupied(1, -1)
                    + occupied(-1, 0)
                    + occupied(1, 0)
                    + occupied(-1, 1)
                    + occupied(0, 1)
                    + occupied(1, 1);

                let chair = if chair == b'L' && count == 0 {
                    changed = true;
                    b'#'
                } else if chair == b'#' && count >= 5 {
                    changed = true;
                    b'L'
                } else {
                    chair
                };

                write(x, y, chair);
            }
        }
        changed
    }

    while step(&seats, &mut tmp) {
        std::mem::swap(&mut seats, &mut tmp);
    }
    seats.iter().copied().filter(|&b| b == b'#').count() as i64
}

#[inline(never)]
fn day_12_part_1(data: &str) -> i64 {
    let (x, y, _) = data.lines().fold((0, 0, 0), |(x, y, h), line| {
        let arg = line[1..].parse::<i64>().unwrap();
        match line.as_bytes()[0] {
            b'N' => (x, y + arg, h),
            b'S' => (x, y - arg, h),
            b'E' => (x + arg, y, h),
            b'W' => (x - arg, y, h),
            b'L' => (x, y, h - arg),
            b'R' => (x, y, h + arg),
            b'F' => match h.rem_euclid(360) {
                0 => (x + arg, y, h),   // E
                90 => (x, y - arg, h),  // S
                180 => (x - arg, y, h), // W
                270 => (x, y + arg, h), // N
                _ => panic!(),
            },
            _ => panic!(),
        }
    });
    x.abs() + y.abs()
}

#[inline(never)]
fn day_12_part_2(data: &str) -> i64 {
    let (x, y, _, _) = data
        .lines()
        .fold((0, 0, 10, 1), |(x, y, way_x, way_y), line| {
            let arg = line[1..].parse::<i64>().unwrap();
            fn rotate(x: i64, y: i64, theta: i64) -> (i64, i64) {
                match theta {
                    0 => (x, y),
                    90 => (y, -x),
                    180 => (-x, -y),
                    270 => (-y, x),
                    _ => panic!(),
                }
            }
            match line.as_bytes()[0] {
                b'N' => (x, y, way_x, way_y + arg),
                b'S' => (x, y, way_x, way_y - arg),
                b'E' => (x, y, way_x + arg, way_y),
                b'W' => (x, y, way_x - arg, way_y),
                b'L' => {
                    let (way_x, way_y) = rotate(way_x, way_y, 360 - arg);
                    (x, y, way_x, way_y)
                }
                b'R' => {
                    let (way_x, way_y) = rotate(way_x, way_y, arg);
                    (x, y, way_x, way_y)
                }
                b'F' => (x + way_x * arg, y + way_y * arg, way_x, way_y),
                _ => panic!(),
            }
        });
    x.abs() + y.abs()
}

#[inline(never)]
fn day_13_part_1(data: &str) -> i64 {
    let mut lines = data.lines();
    let ts = lines.next().unwrap().parse::<i64>().unwrap();
    let (wait_time, bus_id) = lines
        .next()
        .unwrap()
        .split(',')
        .filter_map(|s| {
            let bus_id = s.parse::<i64>().ok()?;
            Some((((ts + bus_id - 1) / bus_id) * bus_id - ts, bus_id))
        })
        .min_by_key(|(wait_time, _)| *wait_time)
        .unwrap();
    wait_time * bus_id
}

fn gcd(mut u: u64, mut v: u64) -> u64 {
    if u == 0 {
        return v;
    } else if v == 0 {
        return u;
    }
    let i = u.trailing_zeros();
    u >>= i;
    let j = v.trailing_zeros();
    v >>= j;
    let k = std::cmp::min(i, j);
    loop {
        if u > v {
            std::mem::swap(&mut u, &mut v);
        }
        v -= u;
        if v == 0 {
            return u << k;
        }
        v >>= v.trailing_zeros();
    }
}

fn lcm(a: u64, b: u64) -> u64 {
    a * (b / gcd(a, b))
}

#[inline(never)]
fn day_13_part_2(data: &str) -> i64 {
    let mut step = 1;
    let mut ts = 0;

    for (offset, bus_id) in data
        .lines()
        .nth(1)
        .unwrap()
        .split(',')
        .enumerate()
        .filter_map(|(i, s)| Some((i as u64, s.parse::<u64>().ok()?)))
    {
        while (ts + offset) % bus_id != 0 {
            ts += step;
        }
        step = lcm(step, bus_id);
    }

    ts as i64
}

#[inline(never)]
fn day_14_part_1(data: &str) -> i64 {
    let mut mask_and = !0;
    let mut mask_or = 0;
    let mut mem = HashMap::new();
    for line in data.lines() {
        let mut iter = line.split(" = ");
        let address = iter.next().unwrap();
        let value = iter.next().unwrap();

        if address == "mask" {
            let (zeroes, ones) =
                value
                    .as_bytes()
                    .iter()
                    .enumerate()
                    .fold((0, 0), |(z, o), (i, &b)| {
                        let zero = (b == b'0') as u64;
                        let one = (b == b'1') as u64;
                        (z | zero << (35 - i), o | one << (35 - i))
                    });
            mask_and = !zeroes;
            mask_or = ones;
            continue;
        } else {
            let value = value.parse::<u64>().unwrap();
            mem.insert(address, value & mask_and | mask_or);
        }
    }
    mem.values().sum::<u64>() as i64
}

#[inline(never)]
fn day_14_part_2(data: &str) -> i64 {
    fn permutations<F: FnMut(&mut HashMap<u64, u64>, u64) + Copy>(
        float: u64,
        ones: u64,
        mem: &mut HashMap<u64, u64>,
        mut f: F,
    ) {
        let top_bit = 63 - float.leading_zeros();
        let float = float & !(1 << top_bit);
        if float == 0 {
            f(mem, ones);
            f(mem, ones | (1 << top_bit));
        } else {
            permutations(float, ones, mem, f);
            permutations(float, ones | (1 << top_bit), mem, f);
        }
    }
    let mut mem = HashMap::new();
    let mut ones: u64 = 0;
    let mut floats: u64 = 0;
    for line in data.lines() {
        let mut iter = line.split(" = ");
        let address = iter.next().unwrap();
        let value = iter.next().unwrap();
        if address == "mask" {
            let (o, f) = value
                .as_bytes()
                .iter()
                .enumerate()
                .fold((0, 0), |(o, f), (i, &b)| {
                    let one = (b == b'1') as u64;
                    let float = (b == b'X') as u64;
                    (o | one << (35 - i), f | float << (35 - i))
                });
            ones = o;
            floats = f;
        } else {
            let address = address[4..address.len() - 1].parse::<u64>().unwrap() & !floats;
            let value = value.parse::<u64>().unwrap();
            permutations(floats, ones, &mut mem, |mem, ones| {
                mem.insert(address | ones, value);
            });
        }
    }
    mem.values().sum::<u64>() as i64
}

#[inline(never)]
fn day_15_part_1(data: &str) -> i64 {
    let starting_numbers = data
        .split(',')
        .map(|n| n.parse::<u32>().unwrap())
        .collect::<Vec<_>>();

    let mut numbers_played = vec![0; 2020];
    let mut last_played = *starting_numbers.first().unwrap();
    for turn in 2..=starting_numbers.len() {
        numbers_played[last_played as usize] = turn;
        last_played = starting_numbers[turn - 1];
    }

    for turn in starting_numbers.len() + 1..=2020 {
        let last_heard = numbers_played[last_played as usize];
        let announce = if last_heard != 0 {
            (turn - last_heard) as u32
        } else {
            0
        };
        numbers_played[last_played as usize] = turn;
        last_played = announce;
    }

    last_played as i64
}

#[inline(never)]
fn day_15_part_2(data: &str) -> i64 {
    let starting_numbers = data
        .split(',')
        .map(|n| n.parse::<u32>().unwrap())
        .collect::<Vec<_>>();

    let mut numbers_played = vec![0; 30000000];
    let mut last_played = *starting_numbers.first().unwrap();
    for turn in 2..=starting_numbers.len() {
        let turn = turn as u32;
        numbers_played[last_played as usize] = turn;
        last_played = starting_numbers[(turn - 1) as usize];
    }

    for turn in starting_numbers.len() + 1..=30000000 {
        let turn = turn as u32;
        let last_heard = numbers_played[last_played as usize];
        numbers_played[last_played as usize] = turn;
        let announce = if last_heard != 0 {
            turn - last_heard
        } else {
            0
        };
        last_played = announce;
    }

    last_played as i64
}

fn main() {
    let runner = Runner::new();

    println!(
        "{:<15} | {:<15} | {:<15} | {:<15}",
        "", "Result", "Duration", "Instructions",
    );

    println!("----------------+-----------------+-----------------+--------------");

    let days = [
        [day_01_part_1, day_01_part_2],
        [day_02_part_1, day_02_part_2],
        [day_03_part_1, day_03_part_2],
        [day_04_part_1, day_04_part_2],
        [day_05_part_1, day_05_part_2],
        [day_06_part_1, day_06_part_2],
        [day_07_part_1, day_07_part_2],
        [day_08_part_1, day_08_part_2],
        [day_09_part_1, day_09_part_2],
        [day_10_part_1, day_10_part_2],
        [day_11_part_1, day_11_part_2],
        [day_12_part_1, day_12_part_2],
        [day_13_part_1, day_13_part_2],
        [day_14_part_1, day_14_part_2],
        [day_15_part_1, day_15_part_2],
    ];

    let results = [
        [889779, 76110336],
        [560, 303],
        [203, 3316272960],
        [256, 198],
        [896, 659],
        [6885, 3550],
        [238, 82930],
        [1489, 1539],
        [20874512, 3012420],
        [2432, 453551299002368],
        [2361, 2119],
        [381, 28591],
        [410, 600691418730595],
        [13105044880745, 3505392154485],
        [421, 436],
    ];

    for (i, &[part_1, part_2]) in days.iter().enumerate() {
        let day = i + 1;
        let data = load_day(day);
        let &[part_1_result, part_2_result] = &results[i];
        let result = runner.bench(format!("day {:02}, part 1", day).as_str(), || part_1(&data));
        assert_eq!(result, part_1_result);
        let result = runner.bench("        part 2", || part_2(&data));
        assert_eq!(result, part_2_result);
    }
}
