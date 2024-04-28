#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Helper script to convert the jinja file into our hut.rs file
#
# Use as:
#     $ python3 ./tools/hut-parser.py src/hut.rs.jinja > src/hut.rs && cargo build
#

from pathlib import Path
from dataclasses import dataclass
import argparse
import jinja2
import jinja2.environment
import os
import re
import sys
import functools


def sanitize(s):
    s = re.sub(r"[-‐\t: |/.\n,()]", "", s)
    s = re.sub(r"[+]", "Plus", s)
    s = re.sub(r"[-]", "Minus", s)
    numbers = {
        "1": "One",
        "2": "Two",
        "3": "Three",
        "4": "Four",
        "5": "Five",
        "6": "Six",
        "7": "Seven",
        "8": "Eight",
        "9": "Nine",
        "0": "Zero",
    }
    s = functools.reduce(
        lambda s, kv: re.sub(rf"^({kv[0]})", kv[1], s), numbers.items(), s
    )
    return s


def sanitize_keyboard(s):
    map = {
        "!": "ExclamationMark",
        "@": "At",
        "/": "Slash",
        "#": "Hash",
        "$": "Dollar",
        "%": "Percent",
        "^": "Caret",
        "&": "Ampersand",
        "*": "Star",
        "[": "OpenBracket",
        "]": "CloseBracket",
        "{": "OpenBrace",
        "}": "CloseBrace",
        "(": "OpenParenthesis",
        ")": "CloseParenthesis",
        "'": "SingleQuote",
        '"': "DoubleQuote",
        "<": "LessThan",
        ">": "GreaterThan",
        " and ": "And",
        " ": "",
        ",": "Comma",
        "-": "Minus",
        "+": "Plus",
        "|": "Pipe",
        "?": "QuestionMark",
        "=": "Equals",
        "\\": "Backslash",
        "~": "Tilde",
        ";": "Semicolon",
        ":": "Colon",
        ".": "Period",
    }
    s = functools.reduce(lambda s, kv: s.replace(kv[0], kv[1]), map.items(), s)

    numbers = {
        "1": "One",
        "2": "Two",
        "3": "Three",
        "4": "Four",
        "5": "Five",
        "6": "Six",
        "7": "Seven",
        "8": "Eight",
        "9": "Nine",
        "0": "Zero",
    }
    s = functools.reduce(
        lambda s, kv: re.sub(rf"^({kv[0]})", kv[1], s), numbers.items(), s
    )
    return s


@dataclass
class Usage:
    printable: str  # The string as it was in the data file
    name: str  # Name of the usage sanitized to be a valid identifier
    value: int


@dataclass
class UsagePage:
    printable: str
    name: str
    value: int
    usages: list[Usage]


class SkipFile(Exception):
    pass


def parse_hut_file(file):
    """
    Parse a single HUT file. The file format is a set of lines in three
    formats: ::

        (01)<tab>Usage Page name
        A0<tab>Name
        F0-FF<tab>Reserved for somerange

    All numbers in hex, only one Usage Page per file

    Usages are parsed into a UsagePage containing the Usage
    """
    header = next(file).strip()
    r = re.match(r"^\((?P<value>[A-Fa-f0-9]+)\)\s(?P<name>.*)", header)
    assert r is not None
    assert r["name"]

    printable = r["name"]
    value = int(r["value"], 16)
    name = sanitize(printable)
    usage_page = UsagePage(printable=printable, name=name, value=value, usages=[])

    # Vendor-defined page is hand-coded in hut.rs, it's too special
    if name == "VendorDefinedPage1":
        raise SkipFile

    for line in filter(
        lambda s: s and not s.startswith("#"), map(lambda l: l.strip(), file)
    ):
        # Reserved ranges, e.g  '0B-1F	Reserved'
        r = re.match(r"^([A-Fa-f0-9]+)-((0x)?[A-Fa-f0-9]+)\s(?P<name>.*)", line)
        if r:
            if "reserved" not in r["name"].lower():
                print(line)
            continue

        # Single usage, e.g. 36	Slider
        r = re.match(r"^(?P<usage>[A-Fa-f0-9]+)\s?(?P<name>.*)", line)
        assert r is not None
        if "reserved" in r["name"].lower():
            continue

        printable = r["name"]
        usage = int(r["usage"], 16)
        if usage_page.value == 0x7:  # Keyboard
            name = sanitize_keyboard(printable)
        else:
            name = sanitize(printable)
        # A few of the names have \ or " in them
        printable = printable.replace("\\", "\\\\").replace('"', '\\"')

        usage = Usage(printable=printable, name=name, value=usage)
        usage_page.usages.append(usage)

    return usage_page


def parse_data_files(datadir):
    usage_pages = []
    for file in datadir.glob("*.hut"):
        try:
            with open(file, "r", encoding="utf-8") as f:
                usage_pages.append(parse_hut_file(f))
        except SkipFile:
            pass
    return usage_pages


def generate_source(
    usage_pages: list[UsagePage], template: str
) -> jinja2.environment.TemplateStream:
    data = {}
    data["usage_pages"] = usage_pages

    loader: jinja2.BaseLoader
    if template == "-":
        loader = jinja2.FunctionLoader(lambda _: sys.stdin.read())
        filename = "<stdin>"
    else:
        path = Path(template)
        assert path.exists(), f"Failed to find template {path}"
        filename = path.name
        loader = jinja2.FileSystemLoader(os.fspath(path.parent))

    env = jinja2.Environment(
        loader=loader,
        trim_blocks=True,
        lstrip_blocks=True,
    )
    jtemplate = env.get_template(filename)
    return jtemplate.stream(data)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="-")
    parser.add_argument(
        "--datadir",
        type=Path,
        default=Path("data"),
        help="Path to the directory containing .hut files",
    )
    parser.add_argument("template", type=Path, help="The jinja template file")
    args = parser.parse_args()
    assert args.datadir.exists()
    assert args.template.exists()

    hut = parse_data_files(args.datadir)

    stream = generate_source(usage_pages=hut, template=args.template)
    file = sys.stdout if args.output == "-" else open(args.output, "w")
    stream.dump(file)
