use anyhow::Result;
use clap::{Parser, Subcommand};
use std::path::PathBuf;
#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}
#[derive(Subcommand)]
enum Command {
    /// Export one global graph and shared benchmark input.
    GeneralInput {
        #[arg(long)]
        gates:usize,
        #[arg(long,default_value_t=42)]
        seed:u64,
        #[arg(long,default_value_t=128)]
        max_parties:usize,
        #[arg(long,value_enum,default_value="nand-copy")]
        task:ours_fullnet::general::Task,
        #[arg(long)]
        out:PathBuf,
    },
    /// Verify a general proof using only its public key and statement.
    GeneralVerify {
        #[arg(long)]
        out: PathBuf,
    },
    /// Correctness controls for one global general binary circuit.
    General {
        #[arg(long="gates",alias="constraints", default_value_t = 64)]
        constraints: usize,
        #[arg(long,value_enum,default_value="nand-copy")]
        task:ours_fullnet::general::Task,
        #[arg(long)]
        input:Option<PathBuf>,
        #[arg(long)]
        trace:Option<PathBuf>,
        #[arg(long,default_value_t=520)]
        gamma:usize,
        #[arg(long,default_value_t=4)]
        tau:usize,
        #[arg(long, default_value_t = 42)]
        seed: u64,
        #[arg(long, default_value_t = 16)]
        max_parties: usize,
        #[arg(long, default_value_t = 8)]
        parties: usize,
        #[arg(long)]
        out: PathBuf,
        #[arg(long, default_value_t = 3)]
        index_block_bits: usize,
    },
    /// Benchmark online kernels with in-memory synthetic shares (default: Keccak).
    Benchmark {
        #[arg(long, value_enum, default_value_t = ours_fullnet::application::Application::Keccak)]
        application: ours_fullnet::application::Application,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        trace: PathBuf,
        #[arg(long)]
        parties: usize,
        #[arg(long)]
        messages: usize,
        #[arg(long, default_value_t = 520)]
        gamma: usize,
        #[arg(long, default_value_t = 4)]
        tau: usize,
        #[arg(long)]
        development: bool,
    },
    Prepare {
        #[arg(long, value_enum, default_value_t = ours_fullnet::application::Application::Sha256)]
        application: ours_fullnet::application::Application,
        /// Compatibility alias for --application keccak.
        #[arg(long, conflicts_with = "application")]
        keccak: bool,
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        parties: usize,
        #[arg(long)]
        messages: usize,
        #[arg(long, default_value_t = 520)]
        gamma: usize,
        #[arg(long, default_value_t = 4)]
        tau: usize,
        #[arg(long)]
        development: bool,
    },
    Coordinator {
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        listen: String,
        #[arg(long, value_enum, default_value_t = ours_fullnet::coordinator::MatrixMode::Indexed)]
        matrix_mode: ours_fullnet::coordinator::MatrixMode,
    },
    Worker {
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        party: usize,
        #[arg(long)]
        connect: String,
        #[arg(long)]
        development_delay_command: Option<u8>,
        #[arg(long, default_value_t = 0)]
        development_delay_ms: u64,
    },
    #[command(hide = true)]
    WorkerStdio {
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        party: usize,
    },
    Verify {
        #[arg(long)]
        out: PathBuf,
    },
    /// Execute real party computations sequentially; output a public timing trace.
    Simulate {
        #[arg(long)]
        out: PathBuf,
        #[arg(long)]
        trace: PathBuf,
        #[arg(long)]
        isolate_workers: bool,
    },
}
fn main() -> Result<()> {
    let args=Args::parse();
    let pool=rayon::ThreadPoolBuilder::new().num_threads(1);
    let pool=pool.use_current_thread();
    pool
        .build_global()
        .map_err(anyhow::Error::msg)?;
    match args.command {
        Command::GeneralInput {gates,seed,max_parties,task,out}=>ours_fullnet::general::export_input(gates,seed,max_parties,task,&out),
        Command::GeneralVerify {out} => ours_fullnet::general::verify_files(&out),
        Command::General { constraints, seed, max_parties, parties, task,input,trace,gamma,tau,index_block_bits,out } =>
            ours_fullnet::general::run(constraints,seed,max_parties,parties,task,input.as_deref(),trace.as_deref(),gamma,tau,index_block_bits,&out),
        Command::Benchmark { application, out, trace, parties, messages, gamma, tau, development } =>
            ours_fullnet::benchmark::run(ours_fullnet::prepare::Shape {
                application,layout_version:ours_fullnet::prepare::LAYOUT_VERSION,
                parties,messages,gamma,tau,development,
            },&out,&trace),
        Command::Prepare {
            application,
            keccak,
            input,
            out,
            parties,
            messages,
            gamma,
            tau,
            development,
        } => ours_fullnet::prepare::run(
            ours_fullnet::prepare::Shape {
                application: if keccak { ours_fullnet::application::Application::Keccak } else { application },
                layout_version: ours_fullnet::prepare::LAYOUT_VERSION,
                parties,
                messages,
                gamma,
                tau,
                development,
            },
            &input,
            &out,
        ),
        Command::Coordinator { out, listen, matrix_mode } =>
            ours_fullnet::coordinator::run_with_mode(&out, &listen, matrix_mode),
        Command::Worker {
            out,
            party,
            connect,
            development_delay_command,
            development_delay_ms,
        } => {
            if development_delay_command.is_some() {
                anyhow::ensure!(
                    ours_fullnet::prepare::Shape::read(&out)?.development,
                    "delay hook requires development shape"
                );
            }
            ours_fullnet::worker::run(
                party,
                &out,
                &connect,
                development_delay_command,
                development_delay_ms,
            )
        }
        Command::Verify { out } => ours_fullnet::coordinator::verify(&out),
        Command::WorkerStdio { out, party } => ours_fullnet::worker::run_stdio(party, &out),
        Command::Simulate { out, trace, isolate_workers } => {
            if isolate_workers { ours_fullnet::coordinator::simulate_isolated(&out, &trace) }
            else { ours_fullnet::coordinator::simulate(&out, &trace) }
        },
    }
}
