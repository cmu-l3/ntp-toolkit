"""A script to get the `commit` in a config json"""

import argparse
import json


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '--config',
        default='configs/config.json',
        help='config file'
    )
    args = parser.parse_args()

    with open(args.config) as f:
        sources = json.load(f)
        if not isinstance(sources, list):
            sources = [sources]

    for source in sources:
        print(source['commit'])
