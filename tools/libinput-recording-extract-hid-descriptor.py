#!/usr/bin/env python3
#
# Extracts the 'hid': [1, 2, ...] array from a libinput record output and saves it
# as a file in $PWD, optionally with a prefix.

from pathlib import Path
import argparse
import yaml
import sys


parser = argparse.ArgumentParser(
    description="Script to convert a libinput recording into a binary HID report descriptor"
)
parser.add_argument("recording", type=Path)
parser.add_argument(
    "--prefix", type=str, default="libinput-", help="The prefix for the output file"
)
args = parser.parse_args()

yml = yaml.safe_load(open(args.recording))
try:
    for idx, device in enumerate(yml["devices"]):
        hid = device["hid"]
        # Some recordings have a superfluous null byte at the end
        if hid[-1] == 0x00:
            hid = hid[:-1]
        bus, vid, pid, version = device["evdev"]["id"]
        filename = f"{args.prefix}{bus:04X}:{vid:04X}:{pid:04X}-{idx}.rdesc"
        with open(filename, "wb") as fd:
            fd.write(bytes(hid))
        print(f"{filename}")
except KeyError:
    print(f"Skipping recording {args.recording} with no hid rdesc", file=sys.stderr)
    pass
