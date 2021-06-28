import utils
from verifier import Verifier


if __name__ == '__main__':
    args = utils.parse_arguments()
    utils.set_verbosity(args.verbosity)

    verifier = Verifier(args.json_file, args.function_name, draw_cfg=args.draw_cfg)
    if args.paths:
        verifier.verify_paths()
        verification_succeeded = True
    elif args.manual_horn_clauses:
        verification_succeeded = verifier.verify_program()
    else:
        verification_succeeded = verifier.verify_program_fixed_point()

    if not verification_succeeded:
        utils.rerun_verifier_in_next_mode(args, args.json_file, args.function_name)
