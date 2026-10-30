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
        #[arg(long, default_value_t = 871)]
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
    rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .use_current_thread()
        .build_global()
        .map_err(anyhow::Error::msg)?;
    match Args::parse().command {
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
